/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Abelian extensions
In this file, we define the typeclass of abelian extensions and provide some basic API.
-/

notation3 "Gal(" L "|" K ")" => Gal(L/K)

variable (K L M : Type*) [Field K] [Field L] [Algebra K L]
variable [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- The class of abelian extensions,
defined as galois extensions whose galois group is commutative. -/
class IsAbelianGalois (K L : Type*) [Field K] [Field L] [Algebra K L] : Prop extends
  IsGalois K L, IsMulCommutative Gal(L/K)

instance (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAbelianGalois K L] :
    CommGroup Gal(L/K) where
  mul_comm := Std.Commutative.comm

lemma IsAbelianGalois.tower_bot [IsAbelianGalois K M] :
    IsAbelianGalois K L :=
  have : IsGalois K L :=
    ((AlgEquiv.ofBijective (IsScalarTower.toAlgHom K L M).rangeRestrict
      ⟨RingHom.injective _, AlgHom.rangeRestrict_surjective _⟩).transfer_galois
        (E' := (IsScalarTower.toAlgHom K L M).fieldRange)).mpr
      ((InfiniteGalois.normal_iff_isGalois _).mp inferInstance)
  { is_comm.comm x y := by
      obtain ⟨x, rfl⟩ := AlgEquiv.restrictNormalHom_surjective M x
      obtain ⟨y, rfl⟩ := AlgEquiv.restrictNormalHom_surjective M y
      rw [← map_mul, ← map_mul, mul_comm] }

lemma IsAbelianGalois.tower_top [IsAbelianGalois K M] :
    IsAbelianGalois L M :=
  have : IsGalois L M := .tower_top_of_isGalois K L M
  { is_comm.comm x y := AlgEquiv.restrictScalars_injective K
      (mul_comm (x.restrictScalars K) (y.restrictScalars K)) }

variable {K L M} in
omit [IsScalarTower K L M] [Algebra L M] in
lemma IsAbelianGalois.of_algHom (f : L →ₐ[K] M) [IsAbelianGalois K M] :
    IsAbelianGalois K L :=
  letI := f.toRingHom.toAlgebra
  haveI := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  .tower_bot K L M

instance [IsAbelianGalois K L] (K' : IntermediateField K L) : IsAbelianGalois K K' :=
  .tower_bot K K' L

instance (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAbelianGalois K L]
    (K' : IntermediateField K L) : IsAbelianGalois K' L :=
  .tower_top K _ L

lemma IsAbelianGalois.of_isCyclic [IsGalois K L] [IsCyclic Gal(L/K)] :
    IsAbelianGalois K L :=
  letI := IsCyclic.commGroup (α := Gal(L/K))
  { is_comm.comm x y := mul_comm x y }

variable {K L}

noncomputable
def galSupToProd (E₁ E₂ : IntermediateField K L) [Normal K E₁] [Normal K E₂] :
    Gal((E₁ ⊔ E₂:)|K) →* Gal(E₁|K) × Gal(E₂|K) :=
  letI : Algebra E₁ (E₁ ⊔ E₂:) := (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra
  letI : Algebra E₂ (E₁ ⊔ E₂:) := (IntermediateField.inclusion le_sup_right).toRingHom.toAlgebra
  MonoidHom.prod (AlgEquiv.restrictNormalHom _) (AlgEquiv.restrictNormalHom _)

@[simp]
lemma AlgEquiv.restrictNormalHom_apply' {F : Type*} [Field F] {K₁ : Type*} [Field K₁] [Algebra F K₁]
    (E : Type*) [Field E] [Algebra F E] [Algebra E K₁] [IsScalarTower F E K₁] [Normal F E]
    (σ : K₁ ≃ₐ[F] K₁) (x) :
    algebraMap _ _ (AlgEquiv.restrictNormalHom E σ x) = σ (algebraMap _ _ x) :=
  AlgEquiv.restrictNormal_commutes ..

lemma galSupToProd_injective (E₁ E₂ : IntermediateField K L) [Normal K E₁] [Normal K E₂] :
    Function.Injective (galSupToProd E₁ E₂) := by
  letI : Algebra E₁ (E₁ ⊔ E₂:) := (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra
  letI : Algebra E₂ (E₁ ⊔ E₂:) := (IntermediateField.inclusion le_sup_right).toRingHom.toAlgebra
  intro σ τ h
  ext1 ⟨a, ha⟩
  induction ha using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain (hx | hx) := hx
    · simpa only [galSupToProd, AlgHom.toRingHom_eq_coe, MonoidHom.prod_apply,
        AlgEquiv.restrictNormalHom_apply'] using congr(algebraMap E₁ (E₁ ⊔ E₂:) (($h).1 ⟨x, hx⟩))
    · simpa only [galSupToProd, AlgHom.toRingHom_eq_coe, MonoidHom.prod_apply,
        AlgEquiv.restrictNormalHom_apply'] using congr(algebraMap E₂ (E₁ ⊔ E₂:) (($h).2 ⟨x, hx⟩))
  | algebraMap x =>
    change σ (algebraMap _ _ x) = τ (algebraMap _ _ x)
    simp
  | add x y hx hy _ _ =>
    change σ (⟨x, hx⟩ + ⟨y, hy⟩) = τ (⟨x, hx⟩ + ⟨y, hy⟩)
    simp_all only [map_add]
  | inv x hx _ =>
    change σ (⟨x, hx⟩⁻¹) = τ (⟨x, hx⟩⁻¹)
    simp_all only [map_inv₀]
  | mul x y hx hy _ _ =>
    change σ (⟨x, hx⟩ * ⟨y, hy⟩) = τ (⟨x, hx⟩ * ⟨y, hy⟩)
    simp_all only [map_mul]

lemma IsMulCommutative.of_injective {G H F : Type*} [Mul G] [Mul H] [FunLike F G H]
    [MulHomClass F G H] [IsMulCommutative H] (f : F) (H : Function.Injective f) :
    IsMulCommutative G where
  is_comm.comm x y := H (by simp [IsMulCommutative.is_comm.comm (f x) (f y)])

lemma IsMulCommutative.default {G : Type*} [CommMagma G] : IsMulCommutative G where
  is_comm.comm x y := mul_comm x y

attribute [local instance] IsMulCommutative.default in
lemma IsAbelianGalois.sup (E₁ E₂ : IntermediateField K L)
    [IsAbelianGalois K E₁] [IsAbelianGalois K E₂] : IsAbelianGalois K (E₁ ⊔ E₂ :) := by
  have := IsMulCommutative.of_injective _ (galSupToProd_injective E₁ E₂)
  constructor
