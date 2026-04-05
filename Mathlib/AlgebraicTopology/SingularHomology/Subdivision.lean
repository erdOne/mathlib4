module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.AlgebraicTopology.SingularHomology.SubdivisionDiameter
public import Mathlib.AlgebraicTopology.SingularHomology.Stuff
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Topology.Separation.Lemmas

attribute [simp] Finsupp.support_single_ne_zero

namespace Convexity.StdSimplex
variable (𝕜 ι : Type*) [Semifield 𝕜] [PartialOrder 𝕜] [PosMulReflectLT 𝕜] [IsOrderedRing 𝕜]
  [Fintype ι] [CharZero 𝕜] [Nonempty ι]

end Convexity.StdSimplex

open Convexity

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

section
variable (𝕜 ι : Type*) [Field 𝕜] [PartialOrder 𝕜]
  [PosMulReflectLT 𝕜] [IsOrderedRing 𝕜] [Fintype ι] [CharZero 𝕜] [Nonempty ι]

variable [DecidableEq ι]

variable {X : Type*}

open stdSimplex StdSimplex

end

variable {m n : ℕ}

noncomputable def SimplexCategory.cone (p : Δₜ[n]) (α : Δₜ[m] ⟶ Δₜ[n]) :
    Δₜ[m + 1] ⟶ Δₜ[n] :=
  TopCat.uliftFunctor.{w}.map (TopCat.ofHom (stdSimplex.cone (ULift.down.{w} p)
    ⟨ULift.down.{w} ∘ α.hom ∘ ULift.up.{w}, by fun_prop⟩))

/-- This unification hint helps with problems of the form `(forget ?C).obj R =?= carrier R'`. -/
unif_hint SimplexCategory.len_mk (n : ℕ) where ⊢
  SimplexCategory.len (.mk n) ≟ n

lemma SimplexCategory.δ_apply {n : ℕ} (i : Fin (n + 2)) (j) :
    SimplexCategory.δ i j = i.succAbove j := rfl

lemma stdSimplex.map_δ_apply {n : ℕ} (i : Fin (n + 2)) (j) (σ : stdSimplex ℝ (Fin _)) :
    stdSimplex.map (SimplexCategory.δ i) σ j =
      (if i < j then σ ⟨j - 1, by simpa using j.2⟩ else 0) +
      (if h : i > j then σ ⟨j, by simp_all; lia⟩ else 0) := by
  simp only [_root_.SimplexCategory.len_mk, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply,
    SimplexCategory.δ_apply, Fin.succAbove_eq_iff]
  obtain hij | rfl | hij := lt_trichotomy i j
  · rw [Finset.sum_eq_single ⟨j - 1, by lia⟩]
    all_goals simp; grind
  · rw [Finset.sum_eq_zero]
    all_goals simp <;> grind
  · rw [Finset.sum_eq_single ⟨j, by lia⟩]
    all_goals simp; grind

variable {C} (R : C)

local notation3 "𝒞" => (singularChainComplexFunctor C).obj R

attribute [-simp] stdSimplex.map_coe

@[simp]
lemma toTop_δ_zero_cone {m : ℕ} (p : Δₜ[n]) (α : Δₜ[m] ⟶ Δₜ[n]) :
    SimplexCategory.toTop.map (SimplexCategory.δ 0) ≫ SimplexCategory.cone p α = α := by
  ext σ
  apply ULift.down_injective
  dsimp [SimplexCategory.toTop, TopCat.uliftFunctor, SimplexCategory.cone, ULift.map]
  ext i
  have : (stdSimplex.map (SimplexCategory.δ 0) σ.down) ∘ Fin.succ = σ.down.1 := by
    ext; simp [stdSimplex.map_δ_apply]
  rw [stdSimplex.cone_apply (σ' := σ.down)]
  · simp [stdSimplex.map_δ_apply, convexComboPair_zero]; rfl
  · ext; simp [stdSimplex.map_δ_apply]

@[simp]
lemma toTop_δ_succ_cone {m : ℕ} (p : Δₜ[n]) (α : Δₜ[m + 1] ⟶ Δₜ[n]) (i : Fin (m + 2)) :
    SimplexCategory.toTop.map (SimplexCategory.δ (.succ i)) ≫ SimplexCategory.cone p α =
    SimplexCategory.cone p (SimplexCategory.toTop.{w}.map (SimplexCategory.δ i) ≫ α) := by
  refine TopCat.ext fun σ ↦ ULift.down_injective (stdSimplex.ext (funext fun j ↦ ?_))
  dsimp [SimplexCategory.toTop, TopCat.uliftFunctor, SimplexCategory.cone, ULift.map,
    stdSimplex.cone]
  simp only [_root_.SimplexCategory.len_mk, stdSimplex.map_δ_apply, Fin.not_lt_zero, ↓reduceIte,
    gt_iff_lt, Fin.succ_pos, ↓reduceDIte, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.zero_eta,
    zero_add, stdSimplex.proj]
  congr! with _ h
  ext j
  obtain hij | rfl | hij := lt_trichotomy i j
  · simp [stdSimplex.map_δ_apply, hij, hij.not_gt, show 1 ≤ j.1 by lia]
  · simp [stdSimplex.map_δ_apply]
  · simp [stdSimplex.map_δ_apply, hij, hij.not_gt]

noncomputable
def singularChainComplexCone (m : ℕ) (p : Δₜ[n]) :
    ((𝒞).obj Δₜ[n]).X m ⟶ ((𝒞).obj Δₜ[n]).X (m + 1) :=
  (sigmaConst.obj R).map (ULift.map (SimplexCategory.cone p))

omit [CategoryWithHomology C] in
lemma singularChainComplexCone_d {m : ℕ} (p : Δₜ[n]) :
    singularChainComplexCone R (m + 1) p ≫ ((𝒞).obj _).d (m + 1 + 1) (m + 1) =
      𝟙 _ - ((𝒞).obj _).d (m + 1) m ≫ singularChainComplexCone R m p := by
  apply Sigma.hom_ext _ _ fun i ↦ ?_
  dsimp [singularChainComplexCone, singularChainComplexFunctor, SSet.singularChainComplexFunctor,
    TopCat.toSSet, uliftYoneda]
  simp [Preadditive.comp_sum, Preadditive.sum_comp, SimplicialObject.whiskering,
    SimplicialObject.δ, Fin.sum_univ_succ (n := m + 1 + 1), pow_succ, ← sub_eq_add_neg, ULift.map]
  rfl

omit [CategoryWithHomology C] in
@[reassoc (attr := simp)]
lemma singularChainComplexCone_singularChainComplexFunctor_map
    {R S : C} (f : R ⟶ S) (m : ℕ) (p : Δₜ[n]) :
    singularChainComplexCone R m p ≫ (((singularChainComplexFunctor C).map f).app _).f _ =
      (((singularChainComplexFunctor C).map f).app _).f _ ≫ singularChainComplexCone S m p := by
  apply Sigma.hom_ext _ _ fun i ↦ ?_
  simp [singularChainComplexCone, singularChainComplexFunctor, SSet.singularChainComplexFunctor]

noncomputable
def singularChainComplexSubdivisionAppF : ∀ n,
    (singularChainComplexFunctor C).obj R ⋙ eval _ _ n ⟶
      (singularChainComplexFunctor C).obj R ⋙ eval _ _ n :=
  Nat.rec (𝟙 _) fun n α ↦
    ((singularChainComplexFunctorAdjunction C _).homEquiv _ _).symm
      (Sigma.ι (fun _ ↦ R) ((stdSimplexToTop.app ⦋n + 1⦌).app (.op ⦋n + 1⦌)
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n + 1⦌))) ≫ ((𝒞).obj Δₜ[n + 1]).d (n + 1) n ≫
      α.app _ ≫
        (singularChainComplexCone _ _ ⟨stdSimplex.barycenter _ _⟩))
  -- | 0 => 𝟙 _
  -- | n + 1 =>
  --   ((singularChainComplexFunctorAdjunction C _).homEquiv _ _).symm
  --     (Sigma.ι (fun _ ↦ R) ((stdSimplexToTop.app ⦋n + 1⦌).app (.op ⦋n + 1⦌)
  --       (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n + 1⦌))) ≫ ((𝒞).obj Δₜ[n + 1]).d (n + 1) n ≫
  --     (singularChainComplexSubdivisionAppF n).app _ ≫
  --       (singularChainComplexCone _ _ ⟨stdSimplex.barycenter _ _⟩))

omit [CategoryWithHomology C] in
lemma singularChainComplexSubdivisionAppF_succ :
  singularChainComplexSubdivisionAppF R (n + 1) =
    ((singularChainComplexFunctorAdjunction C _).homEquiv _ _).symm
      (Sigma.ι (fun _ ↦ R) ((stdSimplexToTop.app ⦋n + 1⦌).app (.op ⦋n + 1⦌)
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n + 1⦌))) ≫ ((𝒞).obj Δₜ[n + 1]).d (n + 1) n ≫
      (singularChainComplexSubdivisionAppF R n).app _ ≫
        (singularChainComplexCone _ _ ⟨stdSimplex.barycenter _ _⟩)) := rfl

omit [CategoryWithHomology C] in
lemma singularChainComplexSubdivisionAppF_d (n : ℕ) :
    singularChainComplexSubdivisionAppF R (n + 1) ≫
      (𝒞).whiskerLeft (HomologicalComplex.dNatTrans _ _ _ _) =
      (𝒞).whiskerLeft (HomologicalComplex.dNatTrans _ _ _ _) ≫
      singularChainComplexSubdivisionAppF R n := by
  induction n with
  | zero =>
    apply ((singularChainComplexFunctorAdjunction C _).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right, singularChainComplexSubdivisionAppF,
      singularChainComplexSubdivisionAppF, Equiv.apply_symm_apply]
    have := singularChainComplexCone_d R ⟨stdSimplex.barycenter ℝ (Fin 2)⟩ (m := 0)
    rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq'] at this
    simp [Adjunction.homEquiv, singularChainComplexFunctorAdjunction_unit_app',
        reassoc_of% this]
  | succ n IH =>
    have := congr(($IH).app Δₜ[n + 1 + 1])
    dsimp at this
    apply ((singularChainComplexFunctorAdjunction C _).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right, singularChainComplexSubdivisionAppF_succ,
      Equiv.apply_symm_apply]
    simp [Adjunction.homEquiv, singularChainComplexFunctorAdjunction_unit_app',
      singularChainComplexCone_d, reassoc_of% this]

noncomputable
def singularChainComplexSubdivision :
    singularChainComplexFunctor C ⟶ singularChainComplexFunctor C where
  app R :=
  { app X :=
    { f i := (singularChainComplexSubdivisionAppF R i).app X
      comm' i j e := e ▸ congr(($(singularChainComplexSubdivisionAppF_d R j)).app X) }
    naturality X Y f := by ext i; exact (singularChainComplexSubdivisionAppF R i).naturality _ }
  naturality {R S} f := by
    ext X n
    dsimp
    induction n generalizing X with
    | zero => simp [singularChainComplexSubdivisionAppF]
    | succ n IH =>
      suffices ((Functor.postcompose₂.obj (HomologicalComplex.eval _ _ (n + 1))).obj
            (singularChainComplexFunctor C)).map f ≫ singularChainComplexSubdivisionAppF S (n + 1)
          = singularChainComplexSubdivisionAppF R (n + 1) ≫
        (Functor.whiskerRight ((singularChainComplexFunctor C).map f) (eval _ _ (n + 1))) from
        congr(($this).app X)
      apply ((singularChainComplexFunctorAdjunction C _).homEquiv _ _).injective
      rw [Adjunction.homEquiv_naturality_left,
        singularChainComplexSubdivisionAppF_succ, singularChainComplexSubdivisionAppF_succ,
        Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right,
        Equiv.apply_symm_apply]
      dsimp
      simp only [Category.assoc, singularChainComplexCone_singularChainComplexFunctor_map,
        ← reassoc_of% IH, ← HomologicalComplex.Hom.comm_assoc]
      simp [singularChainComplexFunctor, SSet.singularChainComplexFunctor]

section Homotopy

variable {X Y : TopCat} (f g : X ⟶ Y) (n : ℕ)

open scoped ContinuousMap

theorem singularHomologyFunctor_obj_map_eq_of_homotopic
    (H : ContinuousMap.Homotopic f.hom g.hom) :
    (((singularHomologyFunctor C n).obj R)).map f =
    (((singularHomologyFunctor C n).obj R)).map g :=
  sorry

noncomputable
def singularHomologyFunctorMapHomotopyEquiv (H : X ≃ₕ Y) :
    ((singularHomologyFunctor C n).obj R).obj X ≅ ((singularHomologyFunctor C n).obj R).obj Y where
  hom := ((singularHomologyFunctor C n).obj R).map (TopCat.ofHom H.toFun)
  inv := ((singularHomologyFunctor C n).obj R).map (TopCat.ofHom H.invFun)
  hom_inv_id := by
    rw [← Functor.map_comp, ← TopCat.ofHom_comp,
      singularHomologyFunctor_obj_map_eq_of_homotopic _ _ (𝟙 X) _ (by exact H.left_inv),
      CategoryTheory.Functor.map_id]
  inv_hom_id := by
    rw [← Functor.map_comp, ← TopCat.ofHom_comp,
      singularHomologyFunctor_obj_map_eq_of_homotopic _ _ (𝟙 Y) _ (by exact H.right_inv),
      CategoryTheory.Functor.map_id]

theorem isZero_singularHomologyFunctor_of_contractibleSpace
    (X : TopCat.{w}) [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    IsZero (((singularHomologyFunctor C n).obj R).obj X) := by
  rw [(singularHomologyFunctorMapHomotopyEquiv R n (X := X) (Y := .of PUnit.{w + 1})
    ((ContractibleSpace.hequiv X PUnit.{w + 1}).some)).isZero_iff]
  exact isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ _ _ _ hn

noncomputable
instance : Unique (⊤_ TopCat.{u}) :=
  (asIso (terminalComparison (forget TopCat.{u}))).toEquiv.symm.uniqueCongr inferInstance

instance (X : TopCat.{w}) [ContractibleSpace X] (n : ℕ) :
    IsIso (((singularHomologyFunctor C n).obj R).map (terminal.from X)) := by
  convert (singularHomologyFunctorMapHomotopyEquiv R n (X := X) (Y := ⊤_ TopCat)
    ((ContractibleSpace.hequiv X (⊤_ TopCat)).some)).isIso_hom
  dsimp [singularHomologyFunctorMapHomotopyEquiv]
  congr
  exact terminal.hom_ext _ _

-- TODO: relax to `PathConnectedSpace`.
noncomputable def singularHomologyFunctorZeroOfContractibleSpace
    (X : TopCat.{w}) [ContractibleSpace X] :
    ((singularHomologyFunctor C 0).obj R).obj X ≅ R :=
    asIso (((singularHomologyFunctor C 0).obj R).map (terminal.from X)) ≪≫
    singularHomologyFunctorZeroOfTotallyDisconnectedSpace _ _ _ ≪≫ coproductUniqueIso _

-- generalize
instance {β : Type*} (g : β → C) [HasCoproduct g] [∀ b, Projective (g b)] : Projective (∐ g) where
  factors f e epi :=
  ⟨Limits.Sigma.desc fun b ↦ Projective.factorThru (Sigma.ι g b ≫ f) e, by cat_disch⟩

@[reassoc (attr := simp)]
lemma ChainComplex.homologyπ_alternatingConstHomologyZero_hom
    {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C] (X : C) :
    (ChainComplex.alternatingConst.obj X).homologyπ 0 ≫
      (ChainComplex.alternatingConstHomologyZero X).hom =
    (ChainComplex.alternatingConst.obj X).iCycles 0 := by
  dsimp [ChainComplex.alternatingConstHomologyZero,
    CategoryTheory.ShortComplex.LeftHomologyData.homologyIso,
    ShortComplex.leftHomologyIso, -ChainComplex.alternatingConst_obj,
    ShortComplex.LeftHomologyData.leftHomologyIso,
    HomologicalComplex.homologyπ, CategoryTheory.ShortComplex.homologyπ]
  simp_rw [Category.assoc, ← ShortComplex.leftHomologyMap'_comp, Category.comp_id]
  have := ((ChainComplex.alternatingConst.obj X).sc 0)
  refine (ShortComplex.leftHomologyπ_naturality' ..).trans ?_
  refine (CategoryTheory.ShortComplex.cyclesMap'_i ..).trans ?_
  simp
  rfl

variable (X) in
noncomputable
def projectiveResolutionOfContractibleSpace [ContractibleSpace X] [HasZeroObject C] [Projective R] :
    ProjectiveResolution R where
  complex := ((singularChainComplexFunctor C).obj R).obj X
  projective n := by
    dsimp [singularChainComplexFunctor, SSet.singularChainComplexFunctor]
    infer_instance
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨Sigma.desc (fun _ ↦ 𝟙 _), by
    dsimp [singularChainComplexFunctor, SSet.singularChainComplexFunctor]
    ext
    simp [SimplicialObject.whiskering, SimplicialObject.δ]⟩
  quasiIso.quasiIsoAt n := by
    obtain rfl | hn := eq_or_ne n 0
    · rw [quasiIsoAt_iff_isIso_homologyMap,
        ← isIso_comp_right_iff _ (HomologicalComplex.singleObjHomologySelfIso _ _ _).hom]
      convert (singularHomologyFunctorZeroOfContractibleSpace R X).isIso_hom
      rw [← cancel_epi (HomologicalComplex.homologyπ ..)]
      dsimp [HomologicalComplex.singleObjCyclesSelfIso_hom,
        singularHomologyFunctorZeroOfContractibleSpace,
        singularHomologyFunctor, singularHomologyFunctorZeroOfTotallyDisconnectedSpace,
        -ChainComplex.alternatingConst_obj]
      simp only [HomologicalComplex.homologyπ_naturality_assoc,
        HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
        HomologicalComplex.singleObjCyclesSelfIso_hom, ChainComplex.single₀_obj_zero,
        ChainComplex.single₀ObjXSelf, Iso.refl_hom, Category.comp_id,
        HomologicalComplex.cyclesMap_i, ChainComplex.toSingle₀Equiv_symm_apply_f_zero,
        Category.assoc, ChainComplex.homologyπ_alternatingConstHomologyZero_hom_assoc,
        HomologicalComplex.cyclesMap_i_assoc]
      congr 1
      apply Sigma.hom_ext _ _ fun i ↦ ?_
      simp [singularChainComplexFunctor, SSet.singularChainComplexFunctor,
        singularChainComplexFunctorIsoOfTotallyDisconnectedSpace,
        alternatingFaceMapComplexConst]
    · rw [quasiIsoAt_iff_exactAt]
      · exact HomologicalComplex.exactAt_single_obj _ _ _ _ hn
      · rw [HomologicalComplex.exactAt_iff_isZero_homology]
        exact isZero_singularHomologyFunctor_of_contractibleSpace _ _ _ hn

instance (X : ObjectProperty.FullSubcategory fun X : TopCat ↦ ContractibleSpace X) :
    ContractibleSpace X.obj := X.2

instance (n) : ContractibleSpace ↑Δₜ[n] := Homeomorph.ulift.contractibleSpace_iff.mpr
  ((convex_stdSimplex _ _).contractibleSpace (Set.nonempty_coe_sort.mp inferInstance))

attribute [local simp] singularChainComplexFunctor SSet.singularChainComplexFunctor
  singularChainComplexFunctorAdjunction_unit_app' in
noncomputable
def singularChainComplexFunctorAdjunctionContractibleSpace :
    (Functor.postcompose₂.obj (eval _ _ n)).obj
    (singularChainComplexFunctor C) ⋙
    (Functor.whiskeringLeft _ _ _).obj (ObjectProperty.ι fun X : TopCat ↦ ContractibleSpace X) ⊣
    (evaluation _ _).obj ⟨SimplexCategory.toTop.obj ⦋n⦌, inferInstance⟩ where
  unit := (singularChainComplexFunctorAdjunction C n).unit
  counit :=
  { app F :=
    { app X := Sigma.desc fun i ↦ F.map ⟨i.down⟩
      naturality {X Y} f := by dsimp; ext; simp [← Functor.map_comp]; rfl } }
  left_triangle_components R := by
    suffices ∀ (X : TopCat) (i : TopCat.toSSet.obj X _⦋n⦌),
        ((TopCat.toSSet.map i.down).app (.op ⦋n⦌)
        ((stdSimplexToTop.app ⦋n⦌).app (.op ⦋n⦌) (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)))) = i by
      dsimp; ext X; dsimp; ext i; simpa using congr(Sigma.ι (fun _ ↦ R) $(this X.obj i))
    intro X i
    apply ULift.down_injective
    simp [TopCat.toSSet]
  right_triangle_components F := by
    simpa [-CategoryTheory.Functor.map_id,
      SimplexCategory.toTop.map_id] using F.map_id ⟨Δₜ[n], inferInstance⟩

@[simps]
def HomologicalComplex.functorEquiv
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms D] [HasZeroObject D]
    {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) :
    HomologicalComplex (C ⥤ D) c ≌ C ⥤ HomologicalComplex D c where
  functor := HomologicalComplex.complexOfFunctorsToFunctorToComplex
  inverse.obj F :=
    { X i := F ⋙ eval _ _ i, d i j := F.whiskerLeft (HomologicalComplex.dNatTrans _ _ _ _) }
  inverse.map {F G} α := { f i := Functor.whiskerRight α _ }
  unitIso := .refl _
  counitIso := .refl _

noncomputable
def HomologicalComplex.singleFunctor
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms D] [HasZeroObject D]
    {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι) :
    (C ⥤ D) ⥤ HomologicalComplex (C ⥤ D) c :=
  (Functor.whiskeringRight _ _ _).obj (HomologicalComplex.single _ _ j) ⋙
    (HomologicalComplex.functorEquiv _).inverse

open _root_.HomologicalComplex in
noncomputable
def HomologicalComplex.singleFunctorIso
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms D] [HasZeroObject D]
    {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι) :
    HomologicalComplex.singleFunctor c j ≅ HomologicalComplex.single (C ⥤ D) c j :=
  NatIso.ofComponents (fun F ↦ (HomologicalComplex.Hom.isoOfComponents (fun i ↦
    NatIso.ofComponents (fun X ↦ if h : i = j then
      (singleObjXIsoOfEq c _ _ _ h) ≪≫ (singleObjXIsoOfEq c _ F _ h).symm.app X else
      IsZero.iso (isZero_single_obj_X c _ _ _ h) (((isZero_single_obj_X _ _ _ _ h).obj _))) <| by
      intro X Y f
      obtain rfl | hi := eq_or_ne i j
      · dsimp [single, singleObjXIsoOfEq, singleFunctor]
        rw! [show (if i = i then F else _) = F by simp]; simp
      · exact IsZero.eq_of_src ((isZero_single_obj_X c _ _ _ hi)) _ _)
      fun k l r ↦ by ext; simp [singleFunctor])) fun {F G} α ↦ by
      ext X
      simp [singleFunctor, single, singleObjXIsoOfEq]

lemma ShortComplex.quasiIso_of_quasiIso_evaluation
    {C D : Type*} [Category* C] [Category* D] [Abelian D]
    {X Y : ShortComplex (C ⥤ D)} (f : X ⟶ Y)
    (hf : ∀ i, ShortComplex.QuasiIso (((evaluation _ _).obj i).mapShortComplex.map f)) :
    ShortComplex.QuasiIso f := by
  refine ⟨?_⟩
  apply (config := { allowSynthFailures := true }) NatIso.isIso_of_isIso_app
  intro i
  exact ((ShortComplex.leftHomologyMapData f X.homologyData.left Y.homologyData.left).map
    ((evaluation _ _).obj i)).quasiIso_iff.mp (hf _)

lemma quasiIsoAt_of_quasiIsoAt_evaluation
    {C D : Type*} [Category* C] [Category* D] [Abelian D]
    {ι : Type*} {c : ComplexShape ι} {X Y : HomologicalComplex (C ⥤ D) c}
    (f : X ⟶ Y) (i)
    (hf : ∀ j, QuasiIsoAt ((((evaluation _ _).obj j).mapHomologicalComplex _).map f) i) :
    QuasiIsoAt f i :=
    (quasiIsoAt_iff ..).mpr (ShortComplex.quasiIso_of_quasiIso_evaluation _
      fun j ↦ (quasiIsoAt_iff ..).mp (hf j))

lemma quasiIso_of_quasiIso_evaluation
    {C D : Type*} [Category* C] [Category* D] [Abelian D]
    {ι : Type*} {c : ComplexShape ι} {X Y : HomologicalComplex (C ⥤ D) c}
    (f : X ⟶ Y) (hf : ∀ i, QuasiIso ((((evaluation _ _).obj i).mapHomologicalComplex _).map f)) :
    QuasiIso f :=
  ⟨fun i ↦ quasiIsoAt_of_quasiIsoAt_evaluation _ _ (fun j ↦ (hf j).1 i)⟩

noncomputable
def projectiveResolutionFunctorOfContractibleSpace
    {C : Type*} [Category* C] [Abelian C] [HasCoproducts.{w} C] (R : C) [Projective R] :
    ProjectiveResolution
      ((Functor.const (ObjectProperty.FullSubcategory
          fun X : TopCat ↦ ContractibleSpace X)).obj R) where
  complex := (HomologicalComplex.functorEquiv _).inverse.obj
    (ObjectProperty.ι _ ⋙ (singularChainComplexFunctor C).obj R)
  projective n := by
    have := singularChainComplexFunctorAdjunctionContractibleSpace (C := C) n
    have := Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms this
    exact this.1 (X := R) inferInstance
  π := by
    refine ?_ ≫ ((HomologicalComplex.singleFunctorIso _ _).app _).hom
    exact
    { f i :=
      { app X := (projectiveResolutionOfContractibleSpace R X.obj).π.f i
        naturality {X Y} f := by
          dsimp [HomologicalComplex.singleFunctor]
          simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, Category.comp_id]
          rw [← HomologicalComplex.comp_f]
          congr 1
          refine (Equiv.eq_symm_apply _).mpr (Subtype.ext (Sigma.hom_ext _ _ fun i ↦ ?_))
          simp [ChainComplex.toSingle₀Equiv, singularChainComplexFunctor,
            SSet.singularChainComplexFunctor, projectiveResolutionOfContractibleSpace] }
      comm' i j r := by
        ext X
        simpa [HomologicalComplex.singleFunctor] using
          (projectiveResolutionOfContractibleSpace R X.obj).π.comm' i j r }
  quasiIso := by
    apply (config := { allowSynthFailures := true }) quasiIso_comp
    apply (config := { allowSynthFailures := true }) quasiIso_of_quasiIso_evaluation
    intro X
    dsimp
    exact (projectiveResolutionOfContractibleSpace R X.obj).quasiIso

noncomputable
def homotopySingularChainComplexSubdivisionContractibleSpaceFuntor
    {C : Type*} [Category* C] [Abelian C] [HasCoproducts.{w} C]
    (R : C) [Projective R] :
    Homotopy ((HomologicalComplex.functorEquiv _).inverse.map
      ((ObjectProperty.ι (fun X : TopCat ↦ ContractibleSpace X)).whiskerLeft
        (singularChainComplexSubdivision.app R))) (𝟙 _) :=
  (projectiveResolutionFunctorOfContractibleSpace R).liftHomotopy (𝟙 _) _ _ (by
      ext; exact (Category.id_comp _).trans (by simp)) ((Category.id_comp _).trans (by simp))

noncomputable
def homotopySingularChainComplexSubdivisionOfContractibleSpace
    {C : Type*} [Category* C] [Abelian C] [HasCoproducts.{w} C]
    (R : C) (X : TopCat) [ContractibleSpace X] [Projective R] :
    Homotopy ((singularChainComplexSubdivision.app R).app X) (𝟙 _) :=
  ((evaluation (ObjectProperty.FullSubcategory (fun X : TopCat ↦ ContractibleSpace X)) _).obj
    ⟨TopCat.of X, ‹_›⟩).mapHomotopy
    (homotopySingularChainComplexSubdivisionContractibleSpaceFuntor R)

instance (n) : ContractibleSpace ↑Δₜ[n] := Homeomorph.ulift.contractibleSpace_iff.mpr
  ((convex_stdSimplex _ _).contractibleSpace (Set.nonempty_coe_sort.mp inferInstance))

theorem _root_.CategoryTheory.Adjunction.homEquiv_symm_map {C : Type*} [Category* C]
    {D : Type*} [Category* D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {Y Y' : D}
    (f : Y ⟶ Y') :
    (adj.homEquiv _ _).symm (G.map f) = adj.counit.app Y ≫ f := by
  simp [Adjunction.homEquiv]

theorem homotopySingularChainComplexSubdivisionOfContractibleSpace_naturality
    {C : Type*} [Category* C] [Abelian C] [HasCoproducts.{w} C]
    (R : C) {X Y : TopCat} [ContractibleSpace X] [ContractibleSpace Y] (f : X ⟶ Y) [Projective R]
    (i j) :
    (((singularChainComplexFunctor C).obj R).map f).f _ ≫
      (homotopySingularChainComplexSubdivisionOfContractibleSpace R Y).hom i j =
    (homotopySingularChainComplexSubdivisionOfContractibleSpace R X).hom i j ≫
      (((singularChainComplexFunctor C).obj R).map f).f _ :=
  ((homotopySingularChainComplexSubdivisionContractibleSpaceFuntor R).hom i j).naturality
    (X := ⟨X, ‹_›⟩) (Y := ⟨Y, ‹_›⟩) ⟨f⟩

theorem ι_homotopySingularChainComplexSubdivisionOfContractibleSpace
    {C : Type*} [Category* C] [Abelian C] [HasCoproducts.{w} C]
    (R : C) {X : TopCat} [ContractibleSpace X] [Projective R] (i j) (σ) :
    Sigma.ι _ σ ≫
      (homotopySingularChainComplexSubdivisionOfContractibleSpace R X).hom i j =
      Sigma.ι (fun _ ↦ R) ((stdSimplexToTop.app ⦋i⦌).app (.op ⦋i⦌)
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋i⦌))) ≫
        (homotopySingularChainComplexSubdivisionOfContractibleSpace R Δₜ[i]).hom i j ≫
        (((singularChainComplexFunctor C).obj R).map σ.down).f j := by
  have := σ.down
  dsimp at this
  convert congr(Sigma.ι _ ((stdSimplexToTop.app ⦋_⦌).app (.op ⦋_⦌)
    (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋_⦌))) ≫
    $(homotopySingularChainComplexSubdivisionOfContractibleSpace_naturality R
    (X := Δₜ[i]) (Y := X) σ.down i j)) using 1
  dsimp [singularChainComplexFunctor, SSet.singularChainComplexFunctor]
  simp only [Sigma.ι_comp_map'_assoc, Category.id_comp]
  congr 2
  apply ULift.down_injective
  dsimp
  simp [TopCat.toSSet]

open _root_.HomologicalComplex (dNatTrans)

noncomputable
def homotopySingularChainComplexSubdivisionOfProjective
    {C : Type*} [Category* C] [Abelian C] [HasCoproducts.{w} C]
    (R : C) (X : TopCat) [Projective R] :
    Homotopy ((singularChainComplexSubdivision.app R).app X) (𝟙 _) where
  hom i j :=
    letI e : (singularChainComplexFunctor C).obj R ⋙ eval _ _ i ⟶
      (singularChainComplexFunctor C).obj R ⋙ eval _ _ j :=
      ((singularChainComplexFunctorAdjunction C _).homEquiv _ _).symm
        (Sigma.ι (fun _ ↦ R) ((stdSimplexToTop.app ⦋i⦌).app (.op ⦋i⦌)
          (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋i⦌))) ≫
          (homotopySingularChainComplexSubdivisionOfContractibleSpace R Δₜ[i]).hom i j)
    e.app X
  zero i j h := by
    simp only [evaluation_obj_obj, Functor.comp_obj, HomologicalComplex.eval_obj,
      (homotopySingularChainComplexSubdivisionOfContractibleSpace R Δₜ[i]).zero i j h, comp_zero]
    erw [Adjunction.homAddEquiv_symm_zero]
    rfl
  comm i := by
    letI e (i j) : (singularChainComplexFunctor C).obj R ⋙ eval _ _ i ⟶
      (singularChainComplexFunctor C).obj R ⋙ eval _ _ j :=
      ((singularChainComplexFunctorAdjunction C _).homEquiv _ _).symm
        (Sigma.ι (fun _ ↦ R) ((stdSimplexToTop.app ⦋i⦌).app (.op ⦋i⦌)
          (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋i⦌))) ≫
          (homotopySingularChainComplexSubdivisionOfContractibleSpace R Δₜ[i]).hom i j)
    change (Functor.whiskerRight (singularChainComplexSubdivision.app R) _).app X =
      ((((singularChainComplexFunctor C).obj R).whiskerLeft (dNatTrans _ _ _ _) ≫ e _ _ +
        e _ _ ≫ ((singularChainComplexFunctor C).obj R).whiskerLeft (dNatTrans _ _ _ _)) +
        𝟙 _).app X
    congr 2
    apply ((singularChainComplexFunctorAdjunction C _).homEquiv _ _).injective
    rw [Adjunction.homAddEquiv_add, Adjunction.homAddEquiv_add,
      (singularChainComplexFunctorAdjunction C i).homEquiv_naturality_right (e _ _),
      Equiv.apply_symm_apply]
    have := congr(Sigma.ι (fun x ↦ R) ((stdSimplexToTop.app ⦋i⦌).app (Opposite.op ⦋i⦌)
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋i⦌))) ≫
      $((homotopySingularChainComplexSubdivisionOfContractibleSpace R Δₜ[i]).comm i))
    dsimp at this ⊢
    simp only [Preadditive.comp_add] at this
    simp only [Adjunction.homEquiv, singularChainComplexFunctorAdjunction_unit_app', Category.assoc]
    dsimp
    convert this using 5
    apply Sigma.hom_ext _ _ fun j ↦ ?_
    dsimp [e, Adjunction.homEquiv, fromNext, singularChainComplexFunctor,
      SSet.singularChainComplexFunctor]
    simp only [Sigma.ι_map_assoc, Category.assoc]
    erw [ι_singularChainComplexFunctorAdjunction_counit_app_app C ((ComplexShape.down ℕ).next i)
      ((TopCat.toSSet ⋙ ((Functor.postcompose₂.obj (alternatingFaceMapComplex C)).obj
      (sigmaConst ⋙ SimplicialObject.whiskering (Type w) C)).obj  R) ⋙
      HomologicalComplex.eval C (ComplexShape.down ℕ) i)]
    rw [ι_homotopySingularChainComplexSubdivisionOfContractibleSpace]
    rfl

noncomputable
def liftSigmaConstMap {σ ι : Type w}
    (f : (sigmaConst.obj (AddCommGrpCat.of (ULift.{w} ℤ))).obj σ ⟶
      (sigmaConst.obj (AddCommGrpCat.of (ULift.{w} ℤ))).obj ι) :
    (sigmaConst.obj R).obj σ ⟶ (sigmaConst.obj R).obj ι :=
  Sigma.desc fun i ↦ Finsupp.linearCombination _ (Sigma.ι _)
    ((Sigma.ι _ i ≫ f ≫ Sigma.desc fun i ↦ AddCommGrpCat.ofHom
      (Finsupp.lsingle (R := ℤ) i).toAddMonoidHom) 1)

omit [CategoryWithHomology C] in
@[simp] lemma liftSigmaConstMap_zero {σ ι : Type w} :
    liftSigmaConstMap R (σ := σ) (ι := ι) 0 = 0 := by
  aesop (add simp liftSigmaConstMap)

omit [CategoryWithHomology C] in
@[simp] lemma liftSigmaConstMap_add {σ ι : Type w}
    (f g : (sigmaConst.obj (AddCommGrpCat.of (ULift.{w} ℤ))).obj σ ⟶
      (sigmaConst.obj (AddCommGrpCat.of (ULift.{w} ℤ))).obj ι) :
    liftSigmaConstMap R (f + g) = liftSigmaConstMap R f + liftSigmaConstMap R g := by
  aesop (add simp liftSigmaConstMap)

omit [CategoryWithHomology C] in
@[simp] lemma liftSigmaConstMap_comp {σ τ ι : Type w}
    (f : (sigmaConst.obj (AddCommGrpCat.of (ULift.{w} ℤ))).obj σ ⟶
      (sigmaConst.obj (AddCommGrpCat.of (ULift.{w} ℤ))).obj τ)
    (g : (sigmaConst.obj (AddCommGrpCat.of (ULift.{w} ℤ))).obj τ ⟶
      (sigmaConst.obj (AddCommGrpCat.of (ULift.{w} ℤ))).obj ι) :
    liftSigmaConstMap R (f ≫ g) = liftSigmaConstMap R f ≫ liftSigmaConstMap R g := by
  dsimp only [sigmaConst_obj_obj, liftSigmaConstMap, ULift.smul_def]
  ext i
  simp only [Category.assoc,
    colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app, colimit.ι_desc_assoc, Discrete.functor_obj_eq_as]
  refine .trans ?_ congr($(Finsupp.linearCombination_linear_comp _
    ((Preadditive.rightComp _ _).toIntLinearMap.restrictScalars _)) _)
  dsimp only [Function.comp_def, LinearMap.coe_restrictScalars, AddMonoidHom.coe_toIntLinearMap,
    CategoryTheory.Preadditive.rightComp, AddMonoidHom.mk'_apply]
  simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
  rw [← Finsupp.linearCombination_linearCombination]
  congr 1
  refine .trans ?_ congr($(Finsupp.linearCombination_linear_comp _
    ((g ≫ Limits.Sigma.desc fun i ↦ AddCommGrpCat.ofHom (Finsupp.lsingle (R := ℤ) i).toAddMonoidHom)
    |>.hom.toIntLinearMap.restrictScalars (ULift ℤ))) _).symm
  dsimp
  congr 2
  have : (Limits.Sigma.desc fun i ↦ AddCommGrpCat.ofHom (Finsupp.lsingle (R := ℤ) i).toAddMonoidHom)
      ≫ AddCommGrpCat.ofHom (Finsupp.linearCombination (ULift.{w} ℤ) fun i ↦
        (Sigma.ι (fun x : τ ↦ AddCommGrpCat.of (ULift.{w} ℤ)) i).hom 1).toAddMonoidHom = 𝟙 _ := by
    ext; simp [← map_zsmul]; rfl
  exact congr($this _).symm

omit [CategoryWithHomology C] in
@[simp] lemma liftSigmaConstMap_id {σ : Type w} :
    liftSigmaConstMap R (𝟙 ((sigmaConst.obj (AddCommGrpCat.of (ULift.{w} ℤ))).obj σ)) = 𝟙 _ := by
  aesop (add simp liftSigmaConstMap)

instance : Projective (AddCommGrpCat.of (ULift.{w, 0} ℤ)) where
  factors {M N} f g _ := by
    obtain ⟨a, ha⟩ := (AddCommGrpCat.epi_iff_surjective g).mp ‹_› (f 1)
    refine ⟨AddCommGrpCat.ofHom (uliftZMultiplesHom _ a), AddCommGrpCat.hom_ext ?_⟩
    exact (uliftZMultiplesHom _).symm.injective (by simpa)

@[simp] lemma Preadditive.hom_sum {ι : Type*} (s : Finset ι) {M N : AddCommGrpCat}
    (f : ι → (M ⟶ N)) : (∑ i ∈ s, f i).hom = ∑ i ∈ s, (f i).hom := by
  classical
  induction s using Finset.induction_on with simp_all

omit [CategoryWithHomology C] in
lemma liftSigmaConstMap_singularChainComplexFunctor_d (X) (i) :
    liftSigmaConstMap R ((((singularChainComplexFunctor AddCommGrpCat.{w}).obj
      (.of (ULift.{w} ℤ))).obj X).d (i + 1) i) = ((𝒞).obj X).d (i + 1) i := by
  refine Sigma.hom_ext _ _ fun σ ↦ ?_
  simp only [sigmaConst_obj_obj, liftSigmaConstMap, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app,
    singularChainComplexFunctor, SSet.singularChainComplexFunctor]
  simp only [Functor.comp_obj, Functor.whiskeringLeft_obj_obj, Functor.postcompose₂_obj_obj_obj_obj,
    alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD,
    SimplicialObject.whiskering_obj_obj_obj, sigmaConst_obj_obj, Int.reduceNeg,
    Preadditive.sum_comp, Linear.smul_comp, Preadditive.comp_sum, Linear.comp_smul,
    Preadditive.hom_sum]
  simp only [Int.reduceNeg, AddCommGrpCat.hom_zsmul, AddCommGrpCat.hom_comp,
    AddMonoidHom.finset_sum_apply, AddMonoidHom.smul_apply, AddMonoidHom.coe_comp,
    Function.comp_apply, map_sum, LinearMap.map_smul_of_tower]
  congr! with x hx
  erw [← AddCommGrpCat.comp_apply, ← AddCommGrpCat.comp_apply, Sigma.ι_desc_assoc]
  rw [Category.assoc, Sigma.ι_desc]
  simp [SimplicialObject.whiskering, SimplicialObject.δ]

omit [CategoryWithHomology C] in
lemma liftSigmaConstMap_singularChainComplexFunctor_d' (X) (i j) :
    liftSigmaConstMap R ((((singularChainComplexFunctor AddCommGrpCat.{w}).obj
      (.of (ULift.{w} ℤ))).obj X).d i j) = ((𝒞).obj X).d i j := by
  by_cases h : (ComplexShape.down ℕ).Rel i j
  · obtain rfl : j + 1 = i := by simpa using h
    exact liftSigmaConstMap_singularChainComplexFunctor_d R X j
  · simp [HomologicalComplex.shape _ _ _ h]

omit [CategoryWithHomology C] in
lemma liftSigmaConstMap_singularChainComplexSubdivision (X) (i) :
    liftSigmaConstMap R (((singularChainComplexSubdivision.app
      (AddCommGrpCat.of (ULift.{w, 0} ℤ))).app X).f i) =
      ((singularChainComplexSubdivision.app R).app X).f i := by
  induction i generalizing X with
  | zero =>
    simp only [sigmaConst_obj_obj, singularChainComplexSubdivision, Functor.comp_obj,
      singularChainComplexSubdivisionAppF, Nat.zero_eq, HomologicalComplex.eval_obj]
    exact liftSigmaConstMap_id ..
  | succ n IH =>
    refine Sigma.hom_ext _ _ fun σ ↦ ?_
    simp only [sigmaConst_obj_obj, liftSigmaConstMap, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app,
      singularChainComplexFunctor, SSet.singularChainComplexFunctor] at IH ⊢
    dsimp [singularChainComplexSubdivision, -AddCommGrpCat.hom_comp,
      singularChainComplexSubdivisionAppF_succ,
      Adjunction.homEquiv, singularChainComplexFunctor, SSet.singularChainComplexFunctor,
      SimplicialObject.whiskering] at IH ⊢
    simp only [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD, Functor.comp_obj,
      sigmaConst_obj_obj, Int.reduceNeg, SimplicialObject.δ, Functor.comp_map, sigmaConst_obj_map,
      Preadditive.sum_comp, Linear.smul_comp, Preadditive.comp_sum, Linear.comp_smul,
      Sigma.ι_comp_map'_assoc, Category.id_comp, Category.assoc, Sigma.ι_map_assoc,
      Preadditive.hom_sum, AddCommGrpCat.hom_zsmul, AddMonoidHom.finset_sum_apply,
      AddMonoidHom.smul_apply, map_sum, LinearMap.map_smul_of_tower]
    rw [← IH]
    simp only [Int.reduceNeg, colimit.ι_desc_assoc,
      Discrete.functor_obj_eq_as, Cofan.mk_pt, Cofan.mk_ι_app]
    congr! with x
    erw [ι_singularChainComplexFunctorAdjunction_counit_app_app C _
      ((TopCat.toSSet ⋙ ((Functor.postcompose₂.obj (alternatingFaceMapComplex C)).obj
      (sigmaConst ⋙ SimplicialObject.whiskering (Type w) C)).obj  R) ⋙
      HomologicalComplex.eval C (ComplexShape.down ℕ) _)]
    erw [reassoc_of% ι_singularChainComplexFunctorAdjunction_counit_app_app _ _
      ((TopCat.toSSet ⋙ ((Functor.postcompose₂.obj (alternatingFaceMapComplex AddCommGrpCat)).obj
        (sigmaConst ⋙ Functor.whiskeringRight SimplexCategoryᵒᵖ (Type w) AddCommGrpCat)).obj
          (AddCommGrpCat.of (ULift.{w, 0} ℤ))) ⋙
          HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) (n + 1))]
    dsimp
    generalize (singularChainComplexSubdivisionAppF
      (AddCommGrpCat.of (ULift.{w, 0} ℤ)) n).app Δₜ[n + 1] ((Sigma.ι
      (fun x ↦ AddCommGrpCat.of (ULift.{w, 0} ℤ)) ((TopCat.toSSet.obj Δₜ[n + 1]).map
      (SimplexCategory.δ x).op ((stdSimplexToTop.app ⦋n + 1⦌).app (Opposite.op ⦋n + 1⦌)
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n + 1⦌))))) 1) = t
    dsimp [singularChainComplexFunctor, SSet.singularChainComplexFunctor] at t
    obtain ⟨t', rfl⟩ : ∃ t', Finsupp.linearCombination (ULift.{w, 0} ℤ)
          (Sigma.ι fun a ↦ (AddCommGrpCat.of (ULift.{w} ℤ))) t' 1 = t := by
      let f : (∐ fun x ↦ AddCommGrpCat.of (ULift.{w, 0} ℤ)) ⟶
            AddCommGrpCat.of (TopCat.toSSet.obj Δₜ[n + 1] _⦋n⦌ →₀ ULift.{w, 0} ℤ) :=
          Sigma.desc fun i ↦ AddCommGrpCat.ofHom (Finsupp.singleAddHom i)
      refine ⟨f.hom t, ?_⟩
      have : f ≫ AddCommGrpCat.ofHom (Finsupp.linearCombination
          (ULift.{w, 0} ℤ) (Sigma.ι fun a ↦ AddCommGrpCat.of (ULift.{w, 0} ℤ))).toAddMonoidHom ≫
          (AddCommGrpCat.ofHom ⟨⟨fun f ↦ f 1, by simp⟩, by simp⟩) = 𝟙 _ := by
        ext1
        simp only [colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_pt,
          Cofan.mk_ι_app, Category.comp_id, f]
        ext; simp [← map_zsmul]; rfl
      exact congr($this _)
    induction t' using Finsupp.induction_linear with
    | zero => simp
    | add f g _ _ => simp_all
    | single a b =>
      simp only [Finsupp.linearCombination_single, ULift.smul_def, AddCommGrpCat.hom_zsmul,
        AddMonoidHom.smul_apply, map_zsmul, Linear.smul_comp]
      simp only [← AddCommGrpCat.comp_apply]
      rw [← AddCommGrpCat.comp_apply, ← AddCommGrpCat.comp_apply, ← AddCommGrpCat.comp_apply]
      simp [-AddCommGrpCat.hom_comp, singularChainComplexCone]

noncomputable
def homotopySingularChainComplexSubdivision (R : C) (X : TopCat) :
    Homotopy ((singularChainComplexSubdivision.app R).app X) (𝟙 _) where
  hom i j := liftSigmaConstMap _ ((homotopySingularChainComplexSubdivisionOfProjective _ _).hom i j)
  zero i j r := by simp [(homotopySingularChainComplexSubdivisionOfProjective _ _).zero i j r]
  comm i := by
    have := congr(liftSigmaConstMap R $((homotopySingularChainComplexSubdivisionOfProjective
      (AddCommGrpCat.of (ULift.{w, 0} ℤ)) X).comm i))
    dsimp [HomologicalComplex.dFrom, HomologicalComplex.dTo] at this ⊢
    rw [liftSigmaConstMap_add, liftSigmaConstMap_add, liftSigmaConstMap_comp,
      liftSigmaConstMap_comp, liftSigmaConstMap_singularChainComplexFunctor_d',
      liftSigmaConstMap_singularChainComplexFunctor_d',
      liftSigmaConstMap_singularChainComplexSubdivision] at this
    erw [liftSigmaConstMap_id] at this
    exact this

end Homotopy

section foo

section

variable (M ι : Type u) [AddCommGroup M]

/-- The coproduct cone induced by the concrete coproduct. -/
noncomputable
def finsuppCocone : Cofan fun _ : ι ↦ AddCommGrpCat.of M :=
  Cofan.mk (AddCommGrpCat.of (ι →₀ M)) fun i ↦
    AddCommGrpCat.ofHom (Finsupp.singleAddHom i (M := AddCommGrpCat.of M))

set_option backward.isDefEq.respectTransparency false in
/-- The concrete cocoproduct cone is colimiting. -/
noncomputable
def finsuppCoconeIsColimit : IsColimit (finsuppCocone M ι) where
  desc s := AddCommGrpCat.ofHom (Finsupp.lsum ℤ
    (N := s.pt) (fun i ↦ (s.ι.app ⟨i⟩).hom.toIntLinearMap)).toAddMonoidHom
  fac := by aesop (add simp finsuppCocone)
  uniq s f h := by
    ext : 1; exact Finsupp.addHom_ext fun i x ↦ by simpa using congr($(h ⟨i⟩) (x : M))

end

noncomputable
def AddCommGrpCat.sigmaConstIso (X : Ab.{u}) (σ : Type u) :
    (sigmaConst.obj X).obj σ ≅ .of (σ →₀ X) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (finsuppCoconeIsColimit _ _)

noncomputable
def singularChainComplexFunctor.Chain.mk {M : Ab.{u}} {X : TopCat.{u}} :
    .of (C(stdSimplex ℝ (Fin (n + 1)), X) →₀ M) ≅
      (((singularChainComplexFunctor _).obj M).obj X).X n :=
  (Finsupp.domLCongr (R := ℤ) (TopCat.toSSetObjEquiv _ _).symm).toAddCommGrpIso ≪≫
    (AddCommGrpCat.sigmaConstIso ..).symm

open singularChainComplexFunctor.Chain
end foo

end AlgebraicTopology
