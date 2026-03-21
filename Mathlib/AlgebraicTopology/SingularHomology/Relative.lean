/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib
public import Mathlib.AlgebraicTopology.SingularHomology.Stuff

/-!
# Singular homology

In this file, we define the singular chain complex and singular homology of a topological space.
We also calculate the homology of a totally disconnected space as an example.

-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

instance {ι : Type*} (V : Type*) [Category* V] [HasZeroMorphisms V]
  (c : ComplexShape ι) [HasKernels V] : HasKernels (HomologicalComplex V c) where
  has_limit f :=
    have (n : ι) : HasLimit (parallelPair f 0 ⋙ HomologicalComplex.eval V c n) :=
      hasLimit_of_iso (F := parallelPair (f.f n) 0) (parallelPairIsoMk (.refl _) (.refl _))
    inferInstance

instance {ι : Type*} (V : Type*) [Category* V] [HasZeroMorphisms V]
  (c : ComplexShape ι) [HasCokernels V] : HasCokernels (HomologicalComplex V c) where
  has_colimit f :=
    have (n : ι) : HasColimit (parallelPair f 0 ⋙ HomologicalComplex.eval V c n) :=
      hasColimit_of_iso (F := parallelPair (f.f n) 0) (parallelPairIsoMk (.refl _) (.refl _))
    inferInstance

@[simps]
def CategoryTheory.Limits.cokerShortComplex (C : Type*) [Category* C] [HasZeroMorphisms C]
    [HasCokernels C] : Arrow C ⥤ ShortComplex C where
  obj f := ⟨f.hom, Limits.cokernel.π f.hom, cokernel.condition ..⟩
  map f := ⟨f.left, f.right, ((coker _).map f), by simpa using f.w, by simp⟩

lemma CategoryTheory.Limits.shortExact_cokerShortComplex
    {C : Type*} [Category* C] [Preadditive C]
    [CategoryWithHomology C] [HasCokernels C] (f : Arrow C) [Mono f.hom] :
    ((cokerShortComplex C).obj f).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f.hom)
  mono_f := ‹_›
  epi_g := by dsimp; infer_instance

def ObjectProperty.arrow {C : Type*} [Category* C] (P : MorphismProperty C) :
    ObjectProperty (Arrow C) := (P ·.hom)

namespace AlgebraicTopology

universe w v u

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (n : ℕ)

/-- The relative singular chain complex functor with coefficients in `C`. -/
def relativeSingularChainComplex :
    C ⥤ Arrow TopCat.{w} ⥤ ChainComplex C ℕ :=
  singularChainComplexFunctor C ⋙ CategoryTheory.Functor.mapArrowFunctor _ _ ⋙
    (Functor.whiskeringRight _ _ _).obj (Limits.coker _)

def relativeSingularChainComplex.π :
    singularChainComplexFunctor C ⋙ (Functor.whiskeringLeft _ _ _).obj Arrow.rightFunc ⟶
    relativeSingularChainComplex C :=
  Functor.whiskerLeft (singularChainComplexFunctor C)
    ((Functor.mapArrowFunctor _ _).whiskerLeft
    ((Functor.whiskeringRight _ _ _).map (Limits.coker.π _)))

/-- The `n`-th relative singular homology functor with coefficients in `C`. -/
def relativeSingularShortComplex :
    C ⥤ Arrow TopCat.{w} ⥤ ShortComplex (ChainComplex C ℕ) :=
  singularChainComplexFunctor C ⋙ CategoryTheory.Functor.mapArrowFunctor _ _ ⋙
    (Functor.whiskeringRight _ _ _).obj (Limits.cokerShortComplex _)

/-- The `n`-th relative singular homology functor with coefficients in `C`. -/
def relativeSingularHomologyFunctor : C ⥤ Arrow TopCat.{w} ⥤ C :=
  relativeSingularChainComplex C ⋙
    (Functor.whiskeringRight _ _ _).obj (HomologicalComplex.homologyFunctor _ _ n)

/-- The canonical projection `Hⁿ(X) ⟶ Hⁿ(X, U)` -/
def relativeSingularHomologyFunctor.π :
    singularHomologyFunctor C n ⋙ (Functor.whiskeringLeft _ _ _).obj Arrow.rightFunc ⟶
    relativeSingularHomologyFunctor C n :=
  Functor.whiskerRight (relativeSingularChainComplex.π C)
    ((Functor.whiskeringRight _ _ _).obj (HomologicalComplex.homologyFunctor _ _ n))

set_option backward.isDefEq.respectTransparency false in
instance [Limits.HasPullbacks C] : (alternatingFaceMapComplex C).PreservesMonomorphisms where
  preserves _ _ := HomologicalComplex.mono_of_mono_f _ fun _ ↦ by dsimp; infer_instance

instance {C D E : Type*} [Category* C] [Category* D] [Category* E] (F : D ⥤ E)
    [F.PreservesMonomorphisms] [HasPullbacks D] {G₁ G₂ : C ⥤ D} (α : G₁ ⟶ G₂) [Mono α] :
    Mono (Functor.whiskerRight α F) := by
  apply +allowSynthFailures NatTrans.mono_of_mono_app
  dsimp
  infer_instance

instance {C D E : Type*} [Category* C] [Category* D] [Category* E] (F : D ⥤ E)
    [F.PreservesMonomorphisms] [HasPullbacks D] :
    ((Functor.whiskeringRight C D E).obj F).PreservesMonomorphisms where
  preserves f _ := by dsimp; infer_instance

set_option backward.isDefEq.respectTransparency false in
instance {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    [F.PreservesMonomorphisms] [HasPullbacks C] :
    ((SimplicialObject.whiskering C D).obj F).PreservesMonomorphisms :=
  inferInstanceAs ((Functor.whiskeringRight _ _ _).obj F).PreservesMonomorphisms

instance : TopCat.toSSet.IsRightAdjoint := ⟨_, ⟨sSetTopAdj⟩⟩

set_option backward.isDefEq.respectTransparency false in
instance {X : C} : ((singularChainComplexFunctor C).obj X).PreservesMonomorphisms where
  preserves f _ := by
    dsimp [singularChainComplexFunctor, SSet.singularChainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
    apply +allowSynthFailures Functor.map_mono
    dsimp [SSet] -- Maybe `SSet` should be an abbrev.
    infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The connection map `Hⁿ(X, U) ⟶ Hⁿ⁺¹(U)` on the category of continuous injections `U ⟶ X`. -/
def relativeSingularHomologyFunctor.δNatTrans (m : ℕ) (e : m + 1 = n) :
    relativeSingularHomologyFunctor C n ⋙
      (Functor.whiskeringLeft _ _ _).obj ((ObjectProperty.arrow (.monomorphisms _)).ι) ⟶
    singularHomologyFunctor C m ⋙
      (Functor.whiskeringLeft _ _ _).obj ((ObjectProperty.arrow _).ι ⋙ Arrow.leftFunc) where
  app X :=
  { app f :=
    haveI : Mono f.obj.hom := f.2
    haveI : Mono (((singularChainComplexFunctor C).obj X).mapArrow.obj f.obj).hom := by
      dsimp; infer_instance
    (Limits.shortExact_cokerShortComplex
      (((singularChainComplexFunctor C).obj X).mapArrow.obj f.obj)).δ n m (by simpa)
    naturality {f g} α := (HomologicalComplex.HomologySequence.δ_naturality
      (((relativeSingularShortComplex C).obj X).map _) _ _ _ _ _).symm }
  naturality X Y f := NatTrans.ext <| funext fun α ↦
    (HomologicalComplex.HomologySequence.δ_naturality
      (((relativeSingularShortComplex C).map f).app _) _ _ _ _ _).symm

abbrev relativeSingularHomologyFunctor.δ
    (m : ℕ) (e : m + 1 = n) {U X : TopCat} (f : U ⟶ X)
    (hf : Function.Injective f) (R : C) :
    ((relativeSingularHomologyFunctor C n).obj R).obj (.mk f) ⟶
      ((singularHomologyFunctor C m).obj R).obj U :=
  ((relativeSingularHomologyFunctor.δNatTrans C n m e).app R).app
    ⟨_, (TopCat.mono_iff_injective _).mpr hf⟩

end AlgebraicTopology
