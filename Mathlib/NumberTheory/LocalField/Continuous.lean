/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Henselian

/-!

# Any ring homomorphism between non-archimedean local fields are automatically continuous

-/

open ValuativeRel

variable {K : Type*} [Field K] [TopologicalSpace K] [ValuativeRel K] [IsNonarchimedeanLocalField K]

variable (K) in
noncomputable def residueChar : ℕ := ringChar 𝓀[K]

instance : CharP 𝓀[K] (residueChar K) := inferInstanceAs (CharP _ (ringChar _))

lemma prime_residueChar : (residueChar K).Prime := by
  cases nonempty_fintype 𝓀[K]
  exact (FiniteField.card 𝓀[K] (ringChar 𝓀[K])).choose_spec.1

lemma exists_card_eq_residueChar_pow : ∃ f, Nat.card 𝓀[K] = residueChar K ^ f := by
  cases nonempty_fintype 𝓀[K]
  exact ⟨_, Fintype.card_eq_nat_card.symm.trans
    (FiniteField.card 𝓀[K] (ringChar 𝓀[K])).choose_spec.2⟩

lemma charZero_or_charP_residueChar : CharZero K ∨ CharP K (residueChar K) := by
  have : CharP 𝓀[K] (residueChar K) := inferInstance
  obtain ⟨p, hp⟩ := CharP.exists 𝒪[K]
  obtain rfl | hp0 := eq_or_ne p 0
  · have : CharZero 𝒪[K] := CharP.charP_to_charZero _
    exact .inl (charZero_of_injective_algebraMap (R := 𝒪[K]) Subtype.val_injective)
  · have := CharP.of_ringHom_of_ne_zero (algebraMap 𝒪[K] 𝓀[K]) p hp0
    obtain rfl : p = residueChar K := (CharP.existsUnique 𝓀[K]).unique ‹_› ‹_›
    exact .inr (CharP.of_ringHom_of_ne_zero (algebraMap 𝒪[K] K) _ hp0)

scoped[ValuativeRel] notation3 "q[" K "]" => Nat.card 𝓀[K]
scoped[ValuativeRel] notation3 "p[" K "]" => residueChar K

lemma HenselianLocalRing.of_henselianRing (R : Type*) [CommRing R] [IsLocalRing R]
    [HenselianRing R (IsLocalRing.maximalIdeal R)] : HenselianLocalRing R where
  is_henselian f h₁ h₂ h₃ h₄ := HenselianRing.is_henselian f h₁ h₂ h₃ (h₄.map _)

instance : HenselianLocalRing 𝒪[K] := .of_henselianRing _

open Polynomial in
lemma exists_pow_eq_pow_card_residueField_sub_one_of_valuation_eq_one
    {x : K} (hx : valuation K x = 1) {n : ℕ} (hn : ¬ p[K] ∣ n) :
    ∃ y, y ^ n = x ^ (q[K] - 1) := by
  have h1x : 1 ≤ᵥ x := (valuation K).one_rel_iff.mpr (by simp [hx])
  have hx1 : x ≤ᵥ 1 := (valuation K).rel_one_iff.mpr (by simp [hx])
  obtain ⟨x, rfl⟩ : ∃ y : 𝒪[K], x = y := ⟨⟨x, mem_integers_iff.mpr hx1⟩, rfl⟩
  have : IsUnit (n : 𝒪[K]) := by
    rwa [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast, ne_eq, CharP.cast_eq_zero_iff]
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (X ^ n - C (x ^ (q[K] - 1)))
    (monic_X_pow_sub_C _ (by aesop)) 1 (by
      cases nonempty_fintype 𝓀[K]
      have H : IsLocalRing.residue _ x ≠ 0 := by
        rwa [ne_eq, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff, srel_iff, not_not]
      rw [← IsLocalRing.residue_eq_zero_iff, ← @Fintype.card_eq_nat_card 𝓀[K] inferInstance]
      simp [FiniteField.pow_card_sub_one_eq_one, H]) (by simpa [derivative_X_pow, - map_pow])
  exact ⟨a, by simpa [sub_eq_zero] using ha.map (f := algebraMap 𝒪[K] K)⟩

open Polynomial in
lemma valuation_eq_one_iff {x : K} :
    valuation K x = 1 ↔ x ≠ 0 ∧ ∃ (p q : ℕ), 1 < p ∧ q ≠ 0 ∧ ∀ n, ¬ p ∣ n → ∃ y, y ^ n = x ^ q := by
  constructor
  · intro H
    exact ⟨by aesop, p[K], _, prime_residueChar.one_lt, (Nat.sub_pos_of_lt Finite.one_lt_card).ne',
      fun _ ↦ exists_pow_eq_pow_card_residueField_sub_one_of_valuation_eq_one H⟩
  · rintro ⟨hx₀, p, q, hp, hq, H⟩
    rw [le_antisymm_iff, ← (valuation K).rel_one_iff, ← (valuation K).one_rel_iff]
    wlog hx₁ : x ≤ᵥ 1 generalizing x
    · have := @this x⁻¹ (by simpa) (fun n hn ↦ by obtain ⟨a, ha⟩ := H n hn; exact ⟨a⁻¹, by simpa⟩)
        ((inv_rel_one hx₀).mpr (SRel.rel hx₁))
      rwa [inv_rel_one hx₀, one_rel_inv hx₀, and_comm] at this
    rw [and_iff_right hx₁, ← not_srel_iff]
    intro hx₁
    obtain ⟨n, hn : _ < valuation K x⟩ :=
      exists_pow_lt₀ (uniformizer_lt_one (R := K)) ((Units.mk0 x hx₀).map (valuation K))
    obtain ⟨a, ha⟩ := H (p * (q * n) + 1) (by rw [← Nat.dvd_add_iff_right (by simp)]; aesop)
    by_cases ha1 : 1 ≤ᵥ a
    · have := pow_rel_pow ha1 (p * (q * n) + 1)
      rw [one_pow, ha] at this
      exact absurd this (by simpa using pow_srel_pow hx₁ q hq)
    have :=
      calc uniformizer K ^ (q * n)
      _ ≤ valuation K x ^ q := by rw [pow_mul']; gcongr; simp
      _ = valuation K a ^ (p * (q * n) + 1) := by simp only [← map_pow, ha]
      _ ≤ uniformizer K ^ (p * (q * n) + 1) := by
          have := le_uniformizer_iff.mpr ((valuation K).srel_one_iff.mp ha1); gcongr; simp
    apply lt_irrefl (p * (q * n) + 1)
    rw [pow_le_pow_iff_right_of_lt_one₀ uniformizer_pos uniformizer_lt_one] at this
    calc
    _ ≤ 1 * (q * n) := by simpa only [one_mul] using this
    _ ≤ p * (q * n) := by gcongr
    _ < _ := Nat.lt_succ_self _

variable {L : Type*} [Field L] [TopologicalSpace L] [ValuativeRel L] [IsNonarchimedeanLocalField L]

lemma valuation_map_eq_one
    (f : K →+* L) {x : K} (hx : valuation K x = 1) : valuation L (f x) = 1 := by
  rw [valuation_eq_one_iff] at hx ⊢
  obtain ⟨hx0, p, q, hp, hq, H⟩ := hx
  refine ⟨by simpa, p, q, hp, hq, fun n hn ↦ ?_⟩
  obtain ⟨y, hy⟩ := H n hn
  refine ⟨f y, by simp only [← map_pow, hy]⟩

lemma map_rel_one (f : K →+* L) {x : K} (hx : x ≤ᵥ 1) : f x ≤ᵥ 1 := by
  rw [(valuation _).rel_one_iff] at hx ⊢
  by_contra! hx'
  replace hx : valuation K x < 1 := lt_of_le_of_ne hx (mt (valuation_map_eq_one f) hx'.ne')
  have h₁ := valuation_map_eq_one f ((valuation K).map_one_add_of_lt hx)
  have h₂ := (valuation L).map_add_eq_of_lt_left ((map_one _).trans_lt hx')
  rw [map_add, map_one, add_comm, h₂] at h₁
  exact hx'.ne' h₁

lemma map_srel_one (f : K →+* L) {x : K} (hx : x <ᵥ 1) : f x <ᵥ 1 := by
  let fo : 𝒪[K] →+* 𝒪[L] := f.restrict _ _ (fun _ ↦
    by simpa only [ValuativeRel.mem_integers_iff] using map_rel_one f)
  have : ((IsLocalRing.maximalIdeal 𝒪[L]).comap fo).IsMaximal := by
    rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
    exact @Finite.isField_of_domain _ _ _ (.of_injective (β := 𝓀[L]) _ Ideal.quotientMap_injective)
  have := ((IsLocalRing.isMaximal_iff _).mp this).ge (ValuativeRel.mem_maximalIdeal_iff
    (x := ⟨x, ValuativeRel.mem_integers_iff.mpr hx.rel⟩).mpr hx)
  exact ValuativeRel.mem_maximalIdeal_iff.mp this

instance (f : K →+* L) : ((valuation L).comap f).Compatible where
  rel_iff_le {x y} := by
    by_cases hx : x = 0; · simp [hx]
    by_cases hy : y = 0; · simp [hy]
    simp only [Valuation.comap_apply, ← (valuation L).rel_iff_le]
    constructor
    · rw [← div_rel_one_iff (by simpa), ← div_rel_one_iff (a := f x) (by simpa), ← map_div₀]
      exact map_rel_one f
    · rw [← one_rel_div_iff (by simpa), ← one_rel_div_iff (a := y) (by simpa), ← map_div₀]
      intro h₁
      by_contra h₂
      exact map_srel_one f h₂ h₁

lemma comap_valuation_isEquiv (f : K →+* L) : ((valuation L).comap f).IsEquiv (valuation K) :=
  ValuativeRel.isEquiv _ _

lemma ringHom_continuous (f : K →+* L) : Continuous f := by
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, (IsValuativeTopology.hasBasis_nhds_zero' _).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero' _)]
  intro x hx
  obtain ⟨x, rfl⟩ := valuation_surjective x
  obtain ⟨y, hy⟩ := valuation_surjective (uniformizer K)
  obtain ⟨n, hn⟩ := exists_pow_lt₀ ((comap_valuation_isEquiv f).lt_one_iff_lt_one.mpr
    (hy.trans_lt uniformizer_lt_one)) (.mk0 _ hx)
  refine ⟨valuation K y ^ n, pow_ne_zero _ (by simp [hy]), fun z hz ↦ ?_⟩
  dsimp at hz ⊢
  rw [← map_pow, ← (comap_valuation_isEquiv f).lt_iff_lt, map_pow] at hz
  exact hz.trans hn

instance [Algebra K L] : ValuativeExtension K L where
  rel_iff_rel x y := by
    rw [(valuation L).rel_iff_le, ((valuation L).comap (algebraMap _ _)).rel_iff_le]; rfl

instance [Algebra K L] : ContinuousSMul K L :=
  continuousSMul_of_algebraMap _ _ (ringHom_continuous _)

instance [Algebra K L] : Algebra 𝒪[K] 𝒪[L] where
  smul r s := ⟨(r : K) • s, Algebra.smul_def r.1 s.1 ▸ mul_mem (ValuativeRel.mem_integers_iff.mpr
      (map_rel_one _ (ValuativeRel.mem_integers_iff.mp r.2))) s.2⟩
  algebraMap := (algebraMap K L).restrict _ _ fun _ ↦ by
    simpa only [ValuativeRel.mem_integers_iff] using map_rel_one _
  commutes' _ _ := mul_comm _ _
  smul_def' r s := by ext; simp [← Algebra.smul_def]; rfl

@[simp]
lemma coe_smul [Algebra K L] (r : 𝒪[K]) (s : 𝒪[L]) : ↑(r • s) = (r : K) • (s : L) := rfl

@[simp]
lemma coe_algebraMap [Algebra K L] (r : 𝒪[K]) : algebraMap 𝒪[K] 𝒪[L] r = algebraMap K L r := rfl

instance [Algebra K L] : IsLocalHom (algebraMap 𝒪[K] 𝒪[L]) :=
  ((IsLocalRing.local_hom_TFAE (algebraMap 𝒪[K] 𝒪[L])).out 3 0).mp <| by
    simp only [SetLike.le_def, Ideal.mem_comap, ValuativeRel.mem_maximalIdeal_iff,
      coe_algebraMap]
    exact fun _ ↦ map_srel_one _

instance [Algebra K L] : MulSemiringAction (L ≃ₐ[K] L) 𝒪[L] where
  smul σ x := ⟨σ x, mem_integers_iff.mpr (map_rel_one σ.toRingHom (mem_integers_iff.mp x.2))⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := Subtype.ext <| map_zero _
  smul_add _ _ _ := Subtype.ext <| map_add _ _ _
  smul_one _ := Subtype.ext <| map_one _
  smul_mul _ _ _ := Subtype.ext <| map_mul _ _ _

instance [Algebra K L] :
    SMulCommClass (L ≃ₐ[K] L) 𝒪[K] 𝒪[L] where
  smul_comm σ _ _ := Subtype.ext <| map_smul σ _ _

open IsNonarchimedeanLocalField

lemma valuation_ringEquiv_eq_uniformizer
    (e : K ≃+* L) {x : K} (hx : valuation K x = uniformizer K) :
    valuation L (e x) = uniformizer L := by
  apply le_antisymm
  · rw [le_uniformizer_iff]
    refine ((valuation L).comap e.toRingHom).srel_one_iff.mp ((valuation K).srel_one_iff.mpr ?_)
    exact hx ▸ uniformizer_lt_one
  · obtain ⟨y, hy⟩ := valuation_surjective (uniformizer L)
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [← hy]
    refine ((valuation L).comap e.toRingHom).rel_iff_le.mp ((valuation K).rel_iff_le.mpr ?_)
    rw [hx, le_uniformizer_iff, ← (valuation K).srel_one_iff,
      ((valuation L).comap e.toRingHom).srel_one_iff]
    simpa [hy] using uniformizer_lt_one

lemma valueGroupWithZeroIsoInt_valuation_ringEquiv (e : K ≃+* L) (x : K) :
    valueGroupWithZeroIsoInt L (valuation L (e x)) =
      valueGroupWithZeroIsoInt K (valuation K x) := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨n, hn⟩ := exists_uniformizer_zpow_eq (x := valuation K x) (by simpa)
  rw [← hn]
  obtain ⟨y, hy⟩ := valuation_surjective (uniformizer K)
  rw [← hy, ← map_zpow₀, ← (ValuativeRel.isEquiv ((valuation L).comap e.toRingHom) _).val_eq] at hn
  simp only [RingEquiv.toRingHom_eq_coe, map_zpow₀, Valuation.comap_apply, RingHom.coe_coe,
    valuation_ringEquiv_eq_uniformizer e hy] at hn
  simp [← hn]

lemma valuation_ringEquiv (e : K ≃+* K) (x : K) : valuation K (e x) = valuation K x :=
  (valueGroupWithZeroIsoInt K).injective (valueGroupWithZeroIsoInt_valuation_ringEquiv ..)
