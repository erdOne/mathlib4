/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Valuation.DiscreteValuativeRel
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!

# Definition of (Non-archimedean) local fields

Given a topological field `K` equipped with an equivalence class of valuations (a `ValuativeRel`),
we say that it is a non-archimedean local field if the topology comes from the given valuation,
and it is locally compact and non-discrete.

-/

/--
Given a topological field `K` equipped with an equivalence class of valuations (a `ValuativeRel`),
we say that it is a non-archimedean local field if the topology comes from the given valuation,
and it is locally compact and non-discrete.

This implies the following typeclasses via `inferInstance`
- `IsValuativeTopology K`
- `LocallyCompactSpace K`
- `IsTopologicalDivisionRing K`
- `ValuativeRel.IsNontrivial K`
- `ValuativeRel.IsRankLeOne K`
- `ValuativeRel.IsDiscrete K`
- `IsDiscreteValuationRing 𝒪[K]`
- `Finite 𝓀[K]`

Assuming we have a compatible `UniformSpace K` instance
(e.g. via `IsTopologicalAddGroup.toUniformSpace` and `isUniformAddGroup_of_addCommGroup`) then
- `CompleteSpace K`
- `CompleteSpace 𝒪[K]`
-/
class IsNonarchimedeanLocalField
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] : Prop extends
  IsValuativeTopology K,
  LocallyCompactSpace K,
  ValuativeRel.IsNontrivial K

open ValuativeRel Valued.integer

open scoped WithZero

theorem Irreducible.ne_zero' {K S : Type*} [MonoidWithZero K] [SetLike S K] [SubmonoidClass S K]
    {s : S} {x : s} (h : Irreducible x) : (x : K) ≠ 0 := by
  obtain ⟨x, hx⟩ := x
  rintro rfl
  exact h.1 ((or_self _).mp (h.2 (a := ⟨0, hx⟩) (b := ⟨0, hx⟩) (by ext; simp)))

namespace IsNonarchimedeanLocalField

section TopologicalSpace

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

attribute [local simp] zero_lt_iff

instance : IsTopologicalDivisionRing K := by
  letI := IsTopologicalAddGroup.toUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

lemma isCompact_closedBall (γ : ValueGroupWithZero K) : IsCompact { x | valuation K x ≤ γ } := by
  obtain ⟨γ, rfl⟩ := ValuativeRel.valuation_surjective γ
  by_cases hγ : γ = 0
  · simp [hγ]
  letI := IsTopologicalAddGroup.toUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  obtain ⟨s, hs, -, hs'⟩ := LocallyCompactSpace.local_compact_nhds (0 : K) .univ Filter.univ_mem
  obtain ⟨r, hr, hr1, H⟩ :
      ∃ r', r' ≠ 0 ∧ valuation K r' < 1 ∧ { x | valuation K x ≤ valuation K r' } ⊆ s := by
    obtain ⟨r, hr, hrs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' K).mem_iff.mp hs
    obtain ⟨r', hr', hr⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation K)
    simp only [ne_eq, map_eq_zero] at hr'
    obtain hr1 | hr1 := lt_or_ge r 1
    · obtain ⟨r, rfl⟩ := ValuativeRel.valuation_surjective r
      simp only [ne_eq, map_eq_zero] at hr
      refine ⟨r ^ 2, by simpa using hr, by simpa [pow_two], fun x hx ↦ hrs ?_⟩
      simp only [map_pow, Set.mem_setOf_eq] at hx ⊢
      exact hx.trans_lt (by simpa [pow_two, hr])
    · refine ⟨r', hr', hr, .trans ?_ hrs⟩
      intro x hx
      dsimp at hx ⊢
      exact hx.trans_lt (hr.trans_le hr1)
  convert (hs'.of_isClosed_subset (Valued.isClosed_closedBall K _) H).image
    (Homeomorph.mulLeft₀ (γ / r) (by simp [hr, div_eq_zero_iff, hγ])).continuous using 1
  refine .trans ?_ (Equiv.image_eq_preimage _ _).symm
  ext x
  simp [div_mul_eq_mul_div, div_le_iff₀, IsValuativeTopology.v_eq_valuation, hγ, hr]

instance : CompactSpace 𝒪[K] := isCompact_iff_compactSpace.mp (isCompact_closedBall K 1)

instance (K : Type*) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsValuativeTopology K] : (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)).Compatible :=
  inferInstanceAs (valuation K).Compatible

instance : IsDiscreteValuationRing 𝒪[K] :=
  letI := IsTopologicalAddGroup.toUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  haveI : CompactSpace (Valued.integer K) := inferInstanceAs (CompactSpace 𝒪[K])
  Valued.integer.isDiscreteValuationRing_of_compactSpace

/-- The value group of a local field is (uniquely) isomorphic to `ℤᵐ⁰`. -/
noncomputable
def valueGroupWithZeroIsoInt : ValueGroupWithZero K ≃*o ℤᵐ⁰ := by
  apply Nonempty.some
  letI := IsTopologicalAddGroup.toUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  obtain ⟨_⟩ := Valued.integer.locallyFiniteOrder_units_mrange_of_isCompact_integer
    (isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[K])))
  let e : (MonoidHom.mrange (valuation K)) ≃*o ValueGroupWithZero K :=
    ⟨.ofBijective (MonoidHom.mrange (valuation K)).subtype ⟨Subtype.val_injective, fun x ↦
      ⟨⟨x, ValuativeRel.valuation_surjective x⟩, rfl⟩⟩, .rfl⟩
  have : Nontrivial (ValueGroupWithZero K)ˣ := isNontrivial_iff_nontrivial_units.mp inferInstance
  have : Nontrivial (↥(MonoidHom.mrange (valuation K)))ˣ :=
    (Units.map_injective (f := e.symm.toMonoidHom) e.symm.injective).nontrivial
  exact ⟨e.symm.trans (LocallyFiniteOrder.orderMonoidWithZeroEquiv _)⟩

instance : ValuativeRel.IsDiscrete K :=
  (ValuativeRel.nonempty_orderIso_withZeroMul_int_iff.mp ⟨valueGroupWithZeroIsoInt K⟩).1

instance : ValuativeRel.IsRankLeOne K :=
  ValuativeRel.isRankLeOne_iff_mulArchimedean.mpr
    (.comap (valueGroupWithZeroIsoInt K).toMonoidHom (valueGroupWithZeroIsoInt K).strictMono)

instance : Finite 𝓀[K] :=
  letI := IsTopologicalAddGroup.toUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
    ⟨IsRankLeOne.nonempty.some.emb, IsRankLeOne.nonempty.some.strictMono⟩
  (compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
    (inferInstanceAs (CompactSpace 𝒪[K]))).2.2

instance : T2Space K :=
  letI := IsTopologicalAddGroup.toUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  open scoped Valued in inferInstance

lemma valuation_eq_uniformizer {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    valuation K ϖ = uniformizer K := by
  apply le_antisymm
  · rw [le_uniformizer_iff, ← (valuation K).srel_one_iff, ← mem_maximalIdeal_iff,
      IsLocalRing.mem_maximalIdeal]
    exact hϖ.not_isUnit
  · obtain ⟨x, hx⟩ := valuation_surjective (uniformizer K)


    have := IsDiscreteValuationRing.irreducible_iff_uniformizer


lemma mem_maximalIdeal_pow {x : 𝒪[K]} {n : ℕ} :
    x ∈ 𝓂[K] ^ n ↔ valuation K x ≤ uniformizer K ^ n := by
  constructor
  · intro hx
    induction n generalizing x with
    | zero =>
      simp_rw [pow_zero, ← (valuation K).map_one, ← (valuation K).rel_iff_le, ← mem_integers_iff]
      exact x.2
    | succ n IH =>
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx (fun y hy z hz ↦ ?_) (fun y z ↦ Valuation.map_add_le _)
      rw [Subring.coe_mul, map_mul, pow_succ]
      rw [mem_maximalIdeal_iff, (valuation K).srel_one_iff, ← le_uniformizer_iff] at hz
      exact mul_le_mul (IH hy) hz zero_le' zero_le'
  · intro hx
    obtain ⟨y, hy⟩ := valuation_surjective (uniformizer K)
    have hy0 : y ≠ 0 := fun e ↦ by simpa [e] using hy.symm
    have hyo : y ∈ 𝒪[K] := by
      rw [mem_integers_iff, (valuation K).rel_one_iff, hy]
      exact uniformizer_lt_one.le
    rw [← hy, ← map_pow, ← (valuation K).rel_iff_le, ← div_rel_one_iff (pow_ne_zero _ hy0),
      ← mem_integers_iff] at hx
    rw [← hϖ, ← map_pow, ← Compatible.rel_iff_le, rel_iff_dvd] at hx
    obtain ⟨x, rfl⟩ := hx
    refine Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ?_ _)
    rw [mem_maximalIdeal_iff_valuation_le, hϖ]

lemma isAdic : IsAdic 𝓂[K] := by
  rw [isAdic_iff_hasBasis_zero, Topology.IsEmbedding.subtypeVal.nhds_eq_comap]
  refine ((IsValuativeTopology.hasBasis_nhds_zero' K).comap _).to_hasBasis ?_ ?_
  · simp


proof_wanted isAdicComplete : IsAdicComplete 𝓂[K] 𝒪[K]

@[simp]
lemma valueGroupWithZeroIsoInt_uniformizer :
    valueGroupWithZeroIsoInt K (uniformizer K) = Multiplicative.ofAdd (-1 : ℤ) := by
  apply le_antisymm
  · have : valueGroupWithZeroIsoInt K (uniformizer K) ≠ 0 := by simp
    rw [← WithZero.coe_unzero this, WithZero.coe_le_coe, ← Multiplicative.toAdd_le,
      Int.le_iff_lt_add_one, toAdd_ofAdd, neg_add_cancel, ← Multiplicative.ofAdd_lt,
      ofAdd_toAdd, ofAdd_zero, ← WithZero.coe_lt_coe, WithZero.coe_unzero this]
    exact ((valueGroupWithZeroIsoInt K).toOrderIso.lt_iff_lt.mpr
      uniformizer_lt_one).trans_eq (valueGroupWithZeroIsoInt K).map_one
  · refine (valueGroupWithZeroIsoInt K).toOrderIso.symm_apply_le.mp ?_
    rw [le_uniformizer_iff, OrderIso.symm_apply_lt]
    exact lt_of_lt_of_eq (by decide) (valueGroupWithZeroIsoInt K).map_one.symm

variable {K} in
lemma exists_uniformizer_zpow_eq {x : ValueGroupWithZero K} (hx : x ≠ 0) :
    ∃ n : ℤ, uniformizer K ^ n = x := by
  use - ((valueGroupWithZeroIsoInt K x).unzero (by simpa)).toAdd
  apply (valueGroupWithZeroIsoInt K).injective
  simp [← WithZero.coe_zpow, ← ofAdd_zsmul]

end TopologicalSpace

section UniformSpace

variable (K : Type*) [Field K] [ValuativeRel K]
  [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]

instance : CompleteSpace K :=
  letI : (Valued.v (R := K)).RankOne :=
    ⟨IsRankLeOne.nonempty.some.emb, IsRankLeOne.nonempty.some.strictMono⟩
  open scoped Valued in
  have : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  (properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mp
    inferInstance).1

instance : CompleteSpace 𝒪[K] :=
  letI : (Valued.v (R := K)).RankOne :=
    ⟨IsRankLeOne.nonempty.some.emb, IsRankLeOne.nonempty.some.strictMono⟩
  (compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
    (inferInstanceAs (CompactSpace 𝒪[K]))).1

end UniformSpace

end IsNonarchimedeanLocalField
