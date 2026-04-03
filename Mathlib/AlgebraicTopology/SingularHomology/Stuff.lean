module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.CategoryTheory.Adjunction.Whiskering

@[expose] public section

namespace AlgebraicTopology

set_option backward.isDefEq.respectTransparency false

open SSet CategoryTheory Limits

attribute [-simp] SimplexCategory.toTop_obj SimplexCategory.toTop_map

universe w v u

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C]
variable [Preadditive C] [CategoryWithHomology C] (n : ℕ)

open scoped Simplicial
open HomologicalComplex (eval)

local notation3 "Δₜ[" n "]" => SimplexCategory.toTop.obj ⦋n⦌

@[simps!]
noncomputable def SSet.stdSimplexToTop :
    SSet.stdSimplex.{u} ⟶ SimplexCategory.toTop ⋙ TopCat.toSSet :=
  SSet.stdSimplex.whiskerLeft sSetTopAdj.unit ≫
    Functor.whiskerRight SSet.toTopSimplex.hom TopCat.toSSet

lemma SSet.yonedaEquiv_symm_apply_app {S T : SSet} (f : S ⟶ T) (x : S _⦋n⦌) :
    SSet.yonedaEquiv.symm (f.app (.op ⦋n⦌) x) = SSet.yonedaEquiv.symm x ≫ f := by
  rw [SSet.yonedaEquiv.symm_apply_eq]
  simp [SSet.yonedaEquiv, uliftYonedaEquiv]

@[simp]
lemma SSet.yonedaEquiv_symm_app
    {S : SSet} (n : SimplexCategory) (x : S.obj (.op n)) (α) :
    (SSet.yonedaEquiv.symm x).app (.op n) α = S.map (SSet.stdSimplex.objEquiv α).op x := rfl

@[simp]
lemma SSet.yonedaEquiv_symm_stdSimplex_id (n : SimplexCategory) :
    SSet.yonedaEquiv.symm (SSet.stdSimplex.objEquiv.symm (β := n ⟶ _) (𝟙 n)) = 𝟙 _ :=
  SSet.yonedaEquiv.symm_apply_eq.mpr rfl

lemma sSetTopAdj_unit_app_app_down (S : SSet) (m) (a : S.obj m) :
    ((sSetTopAdj.unit.app S).app m a).down =
      SSet.toTopSimplex.inv.app _ ≫ SSet.toTop.map (SSet.yonedaEquiv.symm a) := by
  delta sSetTopAdj
  rw [Presheaf.uliftYonedaAdjunction_unit_app_app]
  rfl

@[simp]
lemma SSet.stdSimplexToTop_app_app_down (m n) (α) :
    ((stdSimplexToTop.app m).app n α).down =
      SimplexCategory.toTop.map (SSet.stdSimplex.objEquiv α) := by
  dsimp [stdSimplexToTop, TopCat.toSSet]
  erw [sSetTopAdj_unit_app_app_down]
  simp [← IsIso.eq_inv_comp, ← NatTrans.naturality]
  rfl

attribute [local simp] SSet.singularChainComplexFunctor in
attribute [local simp← ] SSet.yonedaEquiv_symm_comp in
noncomputable
def SSet.singularChainComplexFunctorAdjunction : (Functor.postcompose₂.obj (eval _ _ n)).obj
    (SSet.singularChainComplexFunctor C) ⊣ (evaluation _ _).obj Δ[n] where
  unit.app R := Sigma.ι (fun _ : Δ[n] _⦋n⦌ ↦ R) (SSet.stdSimplex.objEquiv (n := ⦋n⦌).symm (𝟙 ⦋n⦌))
  counit.app F := { app S := Sigma.desc fun α ↦ F.map (SSet.yonedaEquiv.symm α) }
  right_triangle_components F := by dsimp; simp

noncomputable
def singularChainComplexFunctorAdjunction : (Functor.postcompose₂.obj (eval _ _ n)).obj
    (singularChainComplexFunctor C) ⊣ (evaluation _ _).obj (SimplexCategory.toTop.obj ⦋n⦌) :=
  ((SSet.singularChainComplexFunctorAdjunction C n).comp (sSetTopAdj.whiskerLeft _)).ofNatIsoRight
    ((evaluation TopCat C).mapIso (SSet.toTopSimplex.app _))

omit [CategoryWithHomology C] in
lemma singularChainComplexFunctorAdjunction_unit_app (R : C) :
    (singularChainComplexFunctorAdjunction C n).unit.app R =
    (SSet.singularChainComplexFunctorAdjunction C n).unit.app R ≫
      (((SSet.singularChainComplexFunctor C).obj R).map (SSet.stdSimplexToTop.app _)).f _ := by
  dsimp [singularChainComplexFunctorAdjunction, Adjunction.ofNatIsoRight,
    Adjunction.equivHomsetRightOfNatIso, Adjunction.homEquiv,
    Adjunction.comp, singularChainComplexFunctor]
  simp [stdSimplexToTop]

omit [CategoryWithHomology C] in
lemma singularChainComplexFunctorAdjunction_unit_app' (R : C) :
    (singularChainComplexFunctorAdjunction C n).unit.app R =
      Sigma.ι (fun _ ↦ R) ((stdSimplexToTop.app ⦋n⦌).app (.op ⦋n⦌)
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))) := by
  dsimp [singularChainComplexFunctorAdjunction, Adjunction.ofNatIsoRight,
    Adjunction.equivHomsetRightOfNatIso, Adjunction.homEquiv,
    Adjunction.comp, singularChainComplexFunctor,
    SSet.singularChainComplexFunctorAdjunction, SSet.singularChainComplexFunctor]
  simp [stdSimplexToTop]

omit [CategoryWithHomology C] in
lemma ι_singularChainComplexFunctorAdjunction_counit_app_app (F : TopCat ⥤ C) (X : TopCat) (i) :
    Sigma.ι _ i ≫ ((singularChainComplexFunctorAdjunction C n).counit.app F).app X =
      F.map i.down := by
  trans F.map (SSet.toTopSimplex.inv.app ⦋n⦌ ≫ SSet.toTop.map (SSet.yonedaEquiv.symm i) ≫
      sSetTopAdj.counit.app X)
  · dsimp [singularChainComplexFunctorAdjunction, Adjunction.ofNatIsoRight,
      Adjunction.equivHomsetRightOfNatIso, Adjunction.homEquiv,
      Adjunction.comp, singularChainComplexFunctor, SSet.singularChainComplexFunctor,
      SSet.singularChainComplexFunctorAdjunction]
    simp
  · congr 1
    rw [← reassoc_of% sSetTopAdj_unit_app_app_down]
    exact congr(($(sSetTopAdj.right_triangle_components X).app (.op ⦋n⦌) i).down)

@[simps]
def _root_.HomologicalComplex.dNatTrans {ι : Type*} (V : Type*) [Category* V] [HasZeroMorphisms V]
    (c : ComplexShape ι) (i j : ι) :
    HomologicalComplex.eval V c i ⟶ HomologicalComplex.eval V c j where
  app X := X.d i j

instance {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : D ⥤ E) [Preadditive D] [Preadditive E] [F.Additive] :
    ((Functor.whiskeringRight C D E).obj F).Additive where

instance {C D E : Type*} [Category* C] [Category* D] [Category* E] [Preadditive E] :
    (Functor.whiskeringRight C D E).Additive where

instance {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) [Preadditive E] : ((Functor.whiskeringLeft C D E).obj F).Additive where

instance {C D E E' : Type*} [Category* C] [Category* D] [Category* E] [Category* E']
    (G : C ⥤ D ⥤ E) (F : E ⥤ E') [Preadditive C] [Preadditive E'] [Preadditive E]
    [F.Additive] [G.Additive] :
    ((Functor.postcompose₂.obj F).obj G).Additive := by
  dsimp [Functor.postcompose₂]
  infer_instance

instance : (sigmaConst.{w} (C := C)).Additive where

instance {C : Type*} [Category* C] [Preadditive C] : Preadditive (SimplicialObject C) :=
  inferInstanceAs (Preadditive (SimplexCategoryᵒᵖ ⥤ C))

instance : (alternatingFaceMapComplex C).Additive where

instance : (SSet.singularChainComplexFunctor C).Additive := by
  have : (Functor.whiskeringRight SimplexCategoryᵒᵖ (Type w) C).Additive := inferInstance -- why?
  delta SSet.singularChainComplexFunctor SimplicialObject.whiskering
  infer_instance

instance : (singularChainComplexFunctor C).Additive := by
  delta singularChainComplexFunctor
  infer_instance

-- instance (X) : ((singularChainComplexFunctor C).obj X).Additive := by
--   delta singularChainComplexFunctor
--   infer_instance

noncomputable
instance : Unique (⊤_ TopCat.{u}) :=
  (asIso (terminalComparison (forget TopCat.{u}))).toEquiv.symm.uniqueCongr inferInstance

-- generalize
instance {β : Type*} (g : β → C) [HasCoproduct g] [∀ b, Projective (g b)] : Projective (∐ g) where
  factors f e epi :=
  ⟨Limits.Sigma.desc fun b ↦ Projective.factorThru (Sigma.ι g b ≫ f) e, by cat_disch⟩

end AlgebraicTopology
