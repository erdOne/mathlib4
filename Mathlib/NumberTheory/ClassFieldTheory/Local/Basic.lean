import Mathlib
import Mathlib.NumberTheory.LocalField.Continuous

universe u

variable (K : Type u) [Field K]

notation3 "Gal(" L:100 "/" K ")" => L ≃ₐ[K] L

section AuxDefs

class IsAbelianGalois (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop extends
  IsGalois K L, IsMulCommutative Gal(L/K)

instance : IsAbelianGalois K K where
  is_comm.comm _ _ := Subsingleton.elim _ _

instance : Algebra.IsQuadraticExtension ℝ ℂ := ⟨by simp⟩
instance : IsAbelianGalois ℝ ℂ where

namespace ValuativeExtension

open ValuativeRel

variable (A B : Type*) [CommRing A] [CommRing B] [ValuativeRel A] [ValuativeRel B]
variable [Algebra A B] [ValuativeExtension A B]

theorem _root_.injective_iff_map_eq_one₀ {G H F} [GroupWithZero G] [CancelMonoidWithZero H]
    [FunLike F G H] [MonoidWithZeroHomClass F G H]
    (f : F) : Function.Injective f ↔ ∀ a, f a = 1 → a = 1 := by
  constructor
  · aesop
  · intros hf a b hab
    have : Nontrivial H := ⟨0, 1, by simpa using hf 0⟩
    obtain rfl | hb := eq_or_ne b 0
    · by_contra ha
      have : f a ≠ 0 := ((Units.mk0 a ha).map
          (MonoidWithZeroHomClass.toMonoidWithZeroHom f).toMonoidHom).ne_zero
      simp [hab] at this
    · have : f b ≠ 0 := ((Units.mk0 b hb).map
        (MonoidWithZeroHomClass.toMonoidWithZeroHom f).toMonoidHom).ne_zero
      simpa [hb] using congr_arg (· * b) (hf (a / b) (by
        apply mul_left_injective₀ this
        simp only [← map_mul, div_mul_cancel₀ a hb, hab, one_mul]))

instance : (valuation A).HasExtension (valuation B) where
  val_isEquiv_comap x y := by
    simp [← Valuation.Compatible.rel_iff_le, ValuativeExtension.rel_iff_rel]

end ValuativeExtension

noncomputable
def normSubgroup (R S : Type*) [CommRing R] [Ring S] [Algebra R S] : Subgroup Rˣ :=
    (Units.map (Algebra.norm R (S := S))).range

@[simp]
lemma normSubgroup_self (R : Type*) [CommRing R] : normSubgroup R R = ⊤ :=
  top_le_iff.mp fun x _ ↦ ⟨x, by simp⟩

lemma normSubgroup_mono {R S T : Type*} [Field R] [Field S] [CommRing T]
    [Algebra R S] [Algebra R T] (f : S →ₐ[R] T) : normSubgroup R T ≤ normSubgroup R S := by
  rintro _ ⟨x, rfl⟩
  letI := f.toRingHom.toAlgebra
  have : IsScalarTower R S T := .of_algebraMap_eq' f.comp_algebraMap.symm
  exact ⟨x.map (Algebra.norm S), by ext; simp [Algebra.norm_norm]⟩

lemma normSubgroup_congr {R S T : Type*} [Field R] [Field S] [Field T]
    [Algebra R S] [Algebra R T] (f : S ≃ₐ[R] T) : normSubgroup R S = normSubgroup R T :=
  (normSubgroup_mono f.symm.toAlgHom).antisymm (normSubgroup_mono f.toAlgHom)

variable {K} in
def IsNormSubgroup (N : Subgroup Kˣ) : Prop :=
  ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
    (_ : IsAbelianGalois K L), N = normSubgroup K L

lemma isNormSubgroup_normSubgroup (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] : IsNormSubgroup (normSubgroup K L) :=
  ⟨L, ‹_›, ‹_›, ‹_›, ‹_›, rfl⟩

lemma isNormSubgroup_top : IsNormSubgroup (⊤ : Subgroup Kˣ) :=
  ⟨K, ‹_›, inferInstance, inferInstance, ⟨⟩, by simp⟩

end AuxDefs

namespace ClassFieldTheory

variable [TopologicalSpace K]

class SatisfiesLocalExistenceTheorem : Prop where
  cond : ∀ (s : Subgroup Kˣ), IsOpen (s : Set Kˣ) ∧ s.FiniteIndex ↔ IsNormSubgroup s

lemma isOpen_normSubgroup [SatisfiesLocalExistenceTheorem K] (L : Type u) [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] : IsOpen (normSubgroup K L : Set Kˣ) :=
  ((SatisfiesLocalExistenceTheorem.cond _).mpr (isNormSubgroup_normSubgroup K L)).1

instance finiteIndex_normSubgroup [SatisfiesLocalExistenceTheorem K] (L : Type u)
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L] :
    (normSubgroup K L).FiniteIndex :=
  ((SatisfiesLocalExistenceTheorem.cond _).mpr (isNormSubgroup_normSubgroup K L)).2

open scoped ValuativeRel in
@[ext]
structure LocalArtinMapData where
  artinMap : ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L], Kˣ ⧸ normSubgroup K L ≃* Gal(L/K)
  isArithFrobAt_artinMap :
    ∀ [ValuativeRel K] [IsNonarchimedeanLocalField K]
    (L : Type u) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel.IsUnramified K L] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ),
    IsArithFrobAt 𝒪[K] (S := 𝒪[L]) (artinMap L (Units.mk0 ϖ.1 hϖ.ne_zero'))
      (IsLocalRing.maximalIdeal _)
  artinMap_algebraMap : ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] (M : Type u) [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsAbelianGalois K M]
    [Algebra L M] [IsScalarTower K L M] (x : Kˣ) (y : L),
    artinMap M x (algebraMap L M y) = algebraMap L M (artinMap L x y)

lemma LocalArtinMapData.restrictNormal_artinMap (Art : LocalArtinMapData K)
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] (M : Type u) [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsAbelianGalois K M]
    [Algebra L M] [IsScalarTower K L M] (x : Kˣ) :
    AlgEquiv.restrictNormal (Art.artinMap M x) L = Art.artinMap L x := by
  ext x
  apply (algebraMap L M).injective
  simp [Art.artinMap_algebraMap]

class SatisfiesLocalClassFieldTheory : Prop where
  satisfiesLocalExistenceTheorem : SatisfiesLocalExistenceTheorem K
  nonempty_localArtinMapData : Nonempty (LocalArtinMapData K)

noncomputable
def localArtinMapData [SatisfiesLocalClassFieldTheory K] : LocalArtinMapData K :=
  Nonempty.some (SatisfiesLocalClassFieldTheory.nonempty_localArtinMapData)

noncomputable
def artinMap [SatisfiesLocalClassFieldTheory K] (L : Type u) [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    Kˣ →* Gal(L/K) :=
  ((localArtinMapData K).artinMap L).toMonoidHom.comp (QuotientGroup.mk' _)

lemma ker_artinMap [SatisfiesLocalClassFieldTheory K] (L : Type u) [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    (artinMap K L).ker = normSubgroup K L := by
  ext; simp [artinMap]

lemma artinMap_surjective [SatisfiesLocalClassFieldTheory K] (L : Type u) [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    Function.Surjective (artinMap K L) :=
  ((localArtinMapData K).artinMap L).surjective.comp Quotient.mk_surjective

lemma restrictNormal_artinMap [SatisfiesLocalClassFieldTheory K]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] (M : Type u) [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsAbelianGalois K M]
    [Algebra L M] [IsScalarTower K L M] (x : Kˣ) :
    AlgEquiv.restrictNormal (artinMap K M x) L = artinMap K L x :=
  (localArtinMapData K).restrictNormal_artinMap ..

@[simp]
lemma artinMap_algebraMap [SatisfiesLocalClassFieldTheory K]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] (M : Type u) [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsAbelianGalois K M]
    [Algebra L M] [IsScalarTower K L M] (x : Kˣ) (a : L) :
    artinMap K M x (algebraMap L M a) = algebraMap L M (artinMap K L x a) := by
  rw [← restrictNormal_artinMap K L M]
  simp

attribute [instance] SatisfiesLocalClassFieldTheory.satisfiesLocalExistenceTheorem

end ClassFieldTheory

section Complex

instance : ConnectedSpace ℂˣ := by
  suffices ConnectedSpace { z : ℂ // z ≠ 0 } from
    let e := unitsHomeomorphNeZero (G₀ := ℂ); e.symm.surjective.connectedSpace e.symm.continuous
  refine isConnected_iff_connectedSpace (s := { z : ℂ | z ≠ 0 }).mp
    (isConnected_compl_singleton_of_one_lt_rank (by simp) _)

instance : ConnectedSpace ℂˣ := by
  suffices ConnectedSpace { z : ℂ // z ≠ 0 } from
    let e := unitsHomeomorphNeZero (G₀ := ℂ); e.symm.surjective.connectedSpace e.symm.continuous
  refine isConnected_iff_connectedSpace (s := { z : ℂ | z ≠ 0 }).mp
    (isConnected_compl_singleton_of_one_lt_rank (by simp) _)

lemma _root_.Subgroup.eq_top_of_isOpen_of_connectedSpace
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ConnectedSpace G]
    (H : Subgroup G) (h : IsOpen (X := G) H) : H = ⊤ :=
  SetLike.coe_injective (((connectedSpace_iff_clopen.mp ‹_›).2 H
    ⟨H.isClosed_of_isOpen h, h⟩).resolve_left (Set.nonempty_iff_ne_empty.mp ⟨(1 : G), H.one_mem⟩))

instance {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ConnectedSpace G] :
    Subsingleton (OpenSubgroup G) :=
  subsingleton_of_forall_eq ⊤ fun H ↦ SetLike.coe_injective <|
    by exact congr($(H.1.eq_top_of_isOpen_of_connectedSpace H.2).1)

lemma Complex.isNormSubgroup_iff {G : Subgroup ℂˣ} : IsNormSubgroup G ↔ G = ⊤ := by
  refine ⟨?_, (· ▸ isNormSubgroup_top ℂ)⟩
  rintro ⟨L, _, _, _, _, rfl⟩
  let e : ℂ ≃ₐ[ℂ] L := .ofBijective (Algebra.ofId _ _)
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  rw [normSubgroup_congr e.symm, normSubgroup_self]

instance : ClassFieldTheory.SatisfiesLocalExistenceTheorem ℂ where
  cond G := by
    rw [Complex.isNormSubgroup_iff]
    refine ⟨fun ⟨h₁, h₂⟩ ↦ ?_, by rintro rfl; exact ⟨isOpen_univ, inferInstance⟩⟩
    exact Subgroup.eq_top_of_isOpen_of_connectedSpace _ h₁

def _root_.MulEquiv.ofSubsingleton
      (G H : Type*) [Monoid G] [Monoid H] [Subsingleton G] [Subsingleton H] :
    G ≃* H where
  toFun := 1
  invFun := 1
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _

instance {R : Type*} [CommRing R] [ValuativeRel R] [TopologicalSpace R] [IsValuativeTopology R]
    [T2Space R] : TotallySeparatedSpace R := by
  refine totallySeparatedSpace_iff_exists_isClopen.mpr fun x y hxy ↦ ?_
  obtain ⟨u, v, hu, hv, hxu, hyv, h₁⟩ := t2_separation hxy
  obtain ⟨w, -, hw⟩ := (IsValuativeTopology.hasBasis_nhds x).mem_iff.mp (hu.mem_nhds hxu)
  exact ⟨_, (IsValuativeTopology.isClopen_ball w).preimage (continuous_sub_right x), by simp,
    fun hy ↦ Set.disjoint_iff.mp h₁ ⟨hw hy, hyv⟩⟩

lemma IsValuativeTopology.not_connectedSpace
    {R : Type*} [CommRing R] [ValuativeRel R] [TopologicalSpace R] [IsValuativeTopology R]
    [T2Space R] [Nontrivial R] : ¬ ConnectedSpace R :=
  fun _ ↦ zero_ne_one ((isPreconnected_univ (α := R)).subsingleton trivial trivial)

noncomputable
def Complex.localArtinMapData : ClassFieldTheory.LocalArtinMapData ℂ where
  artinMap L _ _ _ _ :=
    let e : ℂ ≃ₐ[ℂ] L := .ofBijective (Algebra.ofId _ _)
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    have : Subsingleton (ℂˣ ⧸ normSubgroup ℂ L) := by
      rw [normSubgroup_congr e.symm, normSubgroup_self]
      exact QuotientGroup.subsingleton_quotient_top
    have : Subsingleton Gal(L/ℂ) := (AlgEquiv.autCongr e).symm.subsingleton
    .ofSubsingleton _ _
  isArithFrobAt_artinMap _ _ _ _ _ := by
    cases IsValuativeTopology.not_connectedSpace (inferInstanceAs (ConnectedSpace ℂ))
  artinMap_algebraMap L _ _ _ _ M _ _ _ _ _ _ x y := rfl

instance : ClassFieldTheory.SatisfiesLocalClassFieldTheory ℂ where
  satisfiesLocalExistenceTheorem := inferInstance
  nonempty_localArtinMapData := ⟨Complex.localArtinMapData⟩

end Complex

section Real

open NNReal

#check Nonneg.nontrivial

instance Nonneg.nontrivial' {R : Type*} [One R] [Zero R] [Preorder R]
    [ZeroLEOneClass R] [NeZero (1 : R)] :
    Nontrivial { r : R // 0 ≤ r } :=
  ⟨0, 1, ne_of_apply_ne Subtype.val zero_ne_one⟩

@[simps]
noncomputable
def Nonneg.unitsHomeomorphPos (R : Type*) [DivisionSemiring R] [PartialOrder R] [ZeroLEOneClass R]
    [AddLeftMono R] [PosMulMono R] [PosMulReflectLT R]
    [TopologicalSpace R] [ContinuousInv₀ R] :
    { r : R // 0 ≤ r }ˣ ≃ₜ { r : R // 0 < r } where
  toFun r := ⟨r, lt_of_le_of_ne r.1.2 (Subtype.val_injective.ne r.ne_zero.symm)⟩
  invFun r := ⟨⟨r.1, r.2.le⟩, ⟨r.1⁻¹, inv_nonneg.mpr r.2.le⟩,
    by ext; simp [r.2.ne'], by ext; simp [r.2.ne']⟩
  left_inv r := by ext; rfl
  right_inv r := by ext; rfl
  continuous_toFun := by
    rw [Topology.IsEmbedding.subtypeVal.continuous_iff]
    exact Continuous.subtype_val (p := (0 ≤ ·)) Units.continuous_val
  continuous_invFun := by
    rw [Units.continuous_iff]
    refine ⟨by fun_prop, ?_⟩
    suffices Continuous fun (x : { r : R // 0 < r }) ↦ (x⁻¹ : R) by
      simpa [Topology.IsEmbedding.subtypeVal.continuous_iff, Function.comp_def]
    rw [continuous_iff_continuousAt]
    exact fun x ↦ ContinuousAt.inv₀ (by fun_prop) x.2.ne'

instance : ConnectedSpace ℝ≥0ˣ := by
  suffices ConnectedSpace { r : ℝ // 0 < r } from
    let e := Nonneg.unitsHomeomorphPos ℝ; e.symm.surjective.connectedSpace e.symm.continuous
  refine isConnected_iff_connectedSpace (s := { r : ℝ | 0 < r }).mp isConnected_Ioi

lemma mem_normSubgroup_real_complex_iff {x} :
    x ∈ normSubgroup ℝ ℂ ↔ 0 < (x : ℝ) := by
  constructor
  · rintro ⟨x, rfl⟩; simp [Algebra.norm_complex_eq]
  · exact fun h ↦ ⟨.mk0 (√ x) (by simp [h.le]), by ext; simp [Algebra.norm_complex_eq, h.le]⟩

lemma normSubgroup_real_complex :
    normSubgroup ℝ ℂ = Units.posSubgroup ℝ :=
  Subgroup.ext fun _ ↦ mem_normSubgroup_real_complex_iff

lemma Real.isNormSubgroup_iff {G : Subgroup ℝˣ} :
    IsNormSubgroup G ↔ G = ⊤ ∨ G = Units.posSubgroup ℝ := by
  rw [← normSubgroup_real_complex]
  refine ⟨?_, (Or.elim · (· ▸ isNormSubgroup_top ℝ) (· ▸ isNormSubgroup_normSubgroup ℝ ℂ))⟩
  rintro ⟨L, _, _, _, _, rfl⟩
  obtain ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ := IsAlgClosed.nonempty_algEquiv_or_of_finrank_eq_two L
      Complex.finrank_real_complex <;> simp [normSubgroup_congr e]

lemma Subgroup.isSimpleOrder {G : Type*} [Group G] (hG : Nat.card G = 2) :
    IsSimpleOrder (Subgroup G) where
  __ :=
    have : Finite G := Nat.finite_of_card_ne_zero (by simp [hG])
    Subgroup.nontrivial_iff.mpr (Finite.one_lt_card_iff_nontrivial.mp (by simp [hG]))
  eq_bot_or_eq_top H := by
    have : Finite G := Nat.finite_of_card_ne_zero (by simp [hG])
    have := H.card_le_card_group.trans_eq hG
    have : 0 < Nat.card H := Nat.card_pos
    interval_cases h : Nat.card H
    · simp_all
    · rw [← hG, Subgroup.card_eq_iff_eq_top] at h
      exact .inr h

lemma eq_or_eq_top_of_index_eq_two {G : Type*} [Group G] {H K : Subgroup G}
    (h : K ≤ H) (hK : K.index = 2) : H = K ∨ H = ⊤ := by
  have : K.Normal := Subgroup.normal_of_index_eq_two hK
  have := Subgroup.isSimpleOrder hK
  replace h : (QuotientGroup.mk' K).ker ≤ H := by simpa
  refine (eq_bot_or_eq_top (H.map (QuotientGroup.mk' K))).imp ?_ ?_ <;> intro h'
  · rw [← Subgroup.comap_map_eq_self h, h', MonoidHom.comap_bot, QuotientGroup.ker_mk']
  · rw [← Subgroup.comap_map_eq_self h, h', Subgroup.comap_top]

lemma Units.index_posSubgroup (R : Type*) [Ring R] [LinearOrder R] [IsStrictOrderedRing R] :
    (posSubgroup R).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨-1, fun a ↦ ?_⟩
  obtain h | h := lt_or_gt_of_ne a.ne_zero
  · simp [h, h.le]
  · simp [h, xor_comm, h.le]

lemma Real.isOpen_subgroup_units_iff {G : Subgroup ℝˣ} :
    IsOpen (X := ℝˣ) G ↔ G = ⊤ ∨ G = Units.posSubgroup ℝ := by
  constructor
  · intro h
    have := (G.comap (Units.map NNReal.toRealHom.toMonoidHom)).eq_top_of_isOpen_of_connectedSpace
      (h.preimage (by fun_prop))
    have : Units.posSubgroup ℝ ≤ G := fun r hr ↦ by
      have : _ ∈ G := this.ge (Set.mem_univ ((Nonneg.unitsHomeomorphPos ℝ).symm ⟨r, hr⟩))
      convert this
      ext
      simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe, coe_toRealHom]
      convert (Nonneg.val_unitsHomeomorphPos_symm_apply_coe ℝ ⟨r, hr⟩).symm
    exact (eq_or_eq_top_of_index_eq_two this (Units.index_posSubgroup _)).symm
  · rintro (rfl | rfl)
    · exact isOpen_univ
    · exact (isOpen_Ioi (a := (0 : ℝ))).preimage Units.continuous_val

instance : ClassFieldTheory.SatisfiesLocalExistenceTheorem ℝ where
  cond G := by
    rw [Real.isNormSubgroup_iff, Real.isOpen_subgroup_units_iff, and_iff_left_iff_imp]
    rintro (rfl | rfl)
    · infer_instance
    · rw [Subgroup.finiteIndex_iff, Units.index_posSubgroup]; simp

lemma QuotientGroup.mk_eq_one_iff {G : Type*} [Group G] (H : Subgroup G) [H.Normal] {x : G} :
    (x : G ⧸ H) = 1 ↔ x ∈ H := by
  exact eq_one_iff x

noncomputable
def Real.localArtinMapData : ClassFieldTheory.LocalArtinMapData ℝ where
  artinMap L _ _ _ _ :=
    open scoped Classical in
    if e : Nonempty (L ≃ₐ[ℝ] ℝ) then
      have : Subsingleton (ℝˣ ⧸ normSubgroup ℝ L) := by
        rw [normSubgroup_congr e.some, normSubgroup_self]
        exact QuotientGroup.subsingleton_quotient_top
      have : Subsingleton Gal(L/ℝ) := (AlgEquiv.autCongr e.some).subsingleton
      .ofSubsingleton _ _
    else
      have e := (Real.nonempty_algEquiv_or L).resolve_left e
      mulEquivOfPrimeCardEq (p := 2) (by
        rw [normSubgroup_congr e.some, normSubgroup_real_complex]
        exact Units.index_posSubgroup _) (by
        rw [Nat.card_congr (AlgEquiv.autCongr e.some).toEquiv, IsGalois.card_aut_eq_finrank,
          Complex.finrank_real_complex])
  isArithFrobAt_artinMap _ := by
    cases IsValuativeTopology.not_connectedSpace (inferInstanceAs (ConnectedSpace ℝ))
  artinMap_algebraMap L _ _ _ _ M _ _ _ _ _ _ x y := by
    split_ifs with hM hL hL
    · rfl
    · have ⟨eM⟩ := hM
      have : Function.Surjective (algebraMap L M) := fun x ↦ ⟨algebraMap ℝ L (eM x), by
        trans eM.symm (eM x • 1)
        · rw [← IsScalarTower.algebraMap_apply, Algebra.algebraMap_eq_smul_one, map_smul, map_one]
        · simp⟩
      cases hL ⟨(AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℝ L M)
        ⟨(algebraMap L M).injective, this⟩).trans eM⟩
    · have ⟨eL⟩ := hL
      obtain ⟨y, rfl⟩ : ∃ z, algebraMap ℝ L z = y := ⟨eL y,
        by simpa using congr($(Algebra.ext_id _ (Algebra.ofId ℝ L) eL.symm.toAlgHom) (eL y))⟩
      simp [← IsScalarTower.algebraMap_apply]
    · have eL := ((Real.nonempty_algEquiv_or L).resolve_left hL).some
      have eM := ((Real.nonempty_algEquiv_or M).resolve_left hM).some
      have : Function.Bijective (algebraMap L M) := by
        have := IsAlgClosed.of_ringEquiv _ _ eL.toRingEquiv.symm
        have := IsAlgClosed.of_ringEquiv _ _ eM.toRingEquiv.symm
        have : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite ℝ L M
        have : IsAlgClosure L M := ⟨inferInstance, inferInstance⟩
        let e := IsAlgClosure.equiv L L M
        change Function.Bijective (Algebra.ofId L M)
        rw [Algebra.ext_id _ (Algebra.ofId L M) e.toAlgHom]
        exact e.bijective
      let e : L ≃ₐ[ℝ] M := .ofBijective (Algebra.algHom _ _ _) this
      by_cases hx : x ∈ normSubgroup ℝ L
      · simp [(QuotientGroup.eq_one_iff _).mpr hx,
          (QuotientGroup.eq_one_iff _).mpr ((normSubgroup_congr (eL.trans eM.symm)).le hx)]
      · dsimp
        generalize_proofs _ h₁ h₂ _ h₃ h₄
        trans e.toRingHom ((e.symm.restrictScalars ℝ).autCongr (mulEquivOfPrimeCardEq h₁ h₂ x) y)
        · simp; rfl
        · congr 2
          exact ((Nat.card_eq_two_iff' 1).mp h₄).unique
            (by simpa [-AlgEquiv.autCongr_apply, normSubgroup_congr (eM.trans eL.symm)])
            (by simpa [-AlgEquiv.autCongr_apply])

instance : ClassFieldTheory.SatisfiesLocalClassFieldTheory ℝ where
  satisfiesLocalExistenceTheorem := inferInstance
  nonempty_localArtinMapData := ⟨Real.localArtinMapData⟩

end Real
