import Mathlib

universe u

variable (K : Type u) [Field K]

notation3 "Gal(" L "/" K ")" => Gal(L/K)

section AuxDefs

theorem Irreducible.ne_zero' {K S : Type*} [MonoidWithZero K] [SetLike S K] [SubmonoidClass S K]
    {s : S} {x : s} (h : Irreducible x) : (x : K) ≠ 0 := by
  obtain ⟨x, hx⟩ := x
  rintro rfl
  exact h.1 ((or_self _).mp (h.2 (a := ⟨0, hx⟩) (b := ⟨0, hx⟩) (by ext; simp)))

class IsAbelianGalois (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop extends
  IsGalois K L, IsMulCommutative Gal(L/K)

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

lemma mapValueGroupWithZero_injective : Function.Injective (mapValueGroupWithZero A B) := by
  rw [injective_iff_map_eq_one₀]
  refine ValueGroupWithZero.ind fun x y (h : _ = 1) ↦ ?_
  simpa [ValuativeExtension.rel_iff_rel] using h

class IsUnramified : Prop where
  mapValueGroupWithZero_surjective : Function.Surjective (mapValueGroupWithZero A B)

lemma mapValueGroupWithZero_bijective [IsUnramified A B] :
    Function.Bijective (mapValueGroupWithZero A B) :=
  ⟨mapValueGroupWithZero_injective A B, IsUnramified.mapValueGroupWithZero_surjective⟩

end ValuativeExtension

noncomputable
def normSubgroup (R S : Type*) [CommRing R] [Ring S] [Algebra R S] : Subgroup Rˣ :=
    (Units.map (Algebra.norm R (S := S))).range

variable {K} in
def IsNormSubgroup (N : Subgroup Kˣ) : Prop :=
  ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
    (_ : IsAbelianGalois K L), N = normSubgroup K L

lemma isNormSubgroup_normSubgroup (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] : IsNormSubgroup (normSubgroup K L) :=
  ⟨L, ‹_›, ‹_›, ‹_›, ‹_›, rfl⟩

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

instance [ValuativeRel K] [IsValuativeTopology K]
    (L : Type u) [Field L] [ValuativeRel L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeExtension K L] :
    MulSemiringAction Gal(L/K) ↥(ValuativeRel.valuation L).integer where
  smul σ x := ⟨σ x, sorry⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := Subtype.ext <| map_zero _
  smul_add _ _ _ := Subtype.ext <| map_add _ _ _
  smul_one _ := Subtype.ext <| map_one _
  smul_mul _ _ _ := Subtype.ext <| map_mul _ _ _

instance [ValuativeRel K] [IsValuativeTopology K]
    (L : Type u) [Field L] [ValuativeRel L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] [ValuativeExtension K L] :
    SMulCommClass Gal(L/K) (ValuativeRel.valuation K).integer
      (ValuativeRel.valuation L).integer where
  smul_comm σ _ _ := Subtype.ext <| map_smul σ _ _

open scoped ValuativeRel in
@[ext]
structure LocalArtinMapData where
  artinMap : ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L], Kˣ ⧸ normSubgroup K L ≃* Gal(L/K)
  isArithFrobAt_artinMap :
    ∀ [ValuativeRel K] [IsValuativeTopology K]
    (L : Type u) [Field L] [ValuativeRel L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] [ValuativeExtension K L]
    [ValuativeExtension.IsUnramified K L] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ),
    IsArithFrobAt 𝒪[K] (S := 𝒪[L]) (artinMap L (Units.mk0 ϖ.1 hϖ.ne_zero'))
      (IsLocalRing.maximalIdeal _)
  restrictNormal_artinMap : ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] (M : Type u) [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsAbelianGalois K M]
    [Algebra L M] [IsScalarTower K L M] (x : Kˣ),
    AlgEquiv.restrictNormal (artinMap M x) L = artinMap L x

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
