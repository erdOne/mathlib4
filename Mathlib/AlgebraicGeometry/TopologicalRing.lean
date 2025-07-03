import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Algebra.Category.Ring.Topology
import Mathlib.AlgebraicGeometry.Morphisms.AffineAnd

/-

# Topology on `R`-points of a scheme

If `R` is a local ring, then the `R`-points of `X` is covered by the `R`-points of `Uᵢ` for any
open cover `{ Uᵢ }`. We then give the `R`-points of `X` the topology of the union of the open cover.

## Main result



-/

namespace AlgebraicGeometry

universe u

open CategoryTheory IsLocalRing Topology

variable {R : CommRingCat.{u}} {X Y : Scheme.{u}}

open scoped CommRingCat.HomTopology

instance [TopologicalSpace R] [IsLocalRing R] : TopologicalSpace (Spec R ⟶ X) :=
  .coinduced (fun Uf : Σ U : X.affineOpens, Γ(X, U) ⟶ R ↦ Spec.map (Uf.2) ≫ Uf.1.2.fromSpec)
    inferInstance

variable (R) in
lemma continuous_SpecMap_comp_fromSpec
    [TopologicalSpace R] [IsLocalRing R] (U : X.Opens) (hU : IsAffineOpen U) :
    Continuous (fun f : Γ(X, U) ⟶ R ↦ Spec.map f ≫ hU.fromSpec) :=
  continuous_sigma_iff.mp (continuous_coinduced_rng (β := Spec R ⟶ X)) ⟨U, hU⟩

lemma closedPoint_mem_opensRange [IsLocalRing R]
    {U} (f : Spec R ⟶ X) (g : U ⟶ X) [IsOpenImmersion g] :
    f.base (closedPoint R) ∈ g.opensRange ↔ Set.range f.base ⊆ Set.range g.base := by
  constructor
  · rintro ⟨x, hx⟩ _ ⟨y, rfl⟩
    refine Specializes.mem_open ?_ g.opensRange.2 (Set.mem_range_self x)
    rw [hx]
    exact (specializes_closedPoint y).map f.continuous
  · intro H
    exact H ⟨_, rfl⟩

lemma range_SpecMap_comp_fromSpec [IsLocalRing R]
    (U : X.Opens) (hU : IsAffineOpen U) :
    Set.range (fun f : Γ(X, U) ⟶ R ↦ Spec.map f ≫ hU.fromSpec) =
      { f | f.base (closedPoint R) ∈ U } :=
  subset_antisymm (Set.range_subset_iff.mpr fun _ ↦ (hU.isoSpec.inv.base _).2) fun f hf ↦
    ⟨Spec.preimage (IsOpenImmersion.lift hU.fromSpec f
      ((closedPoint_mem_opensRange _ _).mp <| by simpa)), by simp⟩

variable (R) in
/-- If `U` is affine, the map from `Γ(X, U) ⟶ R` to `Spec R ⟶ X` is an open embedding. -/
lemma isOpenEmbedding_SpecMap_comp_fromSpec
    [TopologicalSpace R] [ContinuousMul R] [IsLocalRing R]
    [IsOpenUnits R] (U : X.Opens) (hU : IsAffineOpen U) :
    IsOpenEmbedding (fun f : Γ(X, U) ⟶ R ↦ Spec.map f ≫ hU.fromSpec) := by
  refine .of_continuous_injective_isOpenMap (continuous_SpecMap_comp_fromSpec R U hU) ?_ ?_
  · exact fun _ _ e ↦ Spec.map_injective ((cancel_mono _).mp e)
  · intro s hs
    rw [isOpen_coinduced, isOpen_sigma_iff]
    intro V
    rw [isOpen_iff_nhds]
    rintro f ⟨g, hg, e : _ ≫ _ = _ ≫ _⟩
    obtain ⟨sU, sV, hs₁, hs₂⟩ := exists_basicOpen_le_affine_inter hU V.2
      ((Spec.map f ≫ V.2.fromSpec).base (IsLocalRing.closedPoint _))
      ⟨by rw [← e]; exact hU.opensRange_fromSpec.le ⟨_, rfl⟩, V.2.opensRange_fromSpec.le ⟨_, rfl⟩⟩
    obtain ⟨φ, rfl⟩ : ∃ φ : Γ(X, X.basicOpen sV) ⟶ R,
        X.presheaf.map (homOfLE (X.basicOpen_le _)).op ≫ φ = f := by
      obtain ⟨φ, hφ⟩ := (range_SpecMap_comp_fromSpec _ (V.2.basicOpen sV)).ge (hs₁ ▸ hs₂)
      refine ⟨φ, Spec.map_injective ((cancel_mono V.2.fromSpec).mp ?_)⟩
      simpa [V.2.map_fromSpec (V.2.basicOpen sV)]
    obtain rfl : X.presheaf.map (homOfLE (hs₁.symm.trans_le (X.basicOpen_le _))).op ≫ φ = g := by
      apply Spec.map_injective
      rw [← cancel_mono hU.fromSpec]
      simpa [V.2.map_fromSpec (V.2.basicOpen sV), hU.map_fromSpec (V.2.basicOpen sV)] using e.symm
    simp only [homOfLE_leOfHom, Filter.le_principal_iff]
    have := V.2.isLocalization_basicOpen
    have := CommRingCat.HomTopology.isOpenEmbedding_precomp_of_isLocalization (R := R)
      (X.presheaf.map (homOfLE (X.basicOpen_le sV)).op) sV
    rw [← this.map_nhds_eq, Filter.mem_map, mem_nhds_iff]
    refine ⟨_, fun f hf ↦ ?_, hs.preimage (CommRingCat.HomTopology.continuous_precomp
      (X.presheaf.map (homOfLE (hs₁.symm.trans_le (X.basicOpen_le sU))).op)), hg⟩
    simp only [homOfLE_leOfHom, Set.mem_preimage, Spec.map_comp, Category.assoc, Set.mem_image]
    refine ⟨_, hf, ?_⟩
    simp [V.2.map_fromSpec (V.2.basicOpen sV), hU.map_fromSpec (V.2.basicOpen sV)]

/-- If `U` is affine, the map from `Γ(X, U) ⟶ R` to `Spec R ⟶ X` is an open embedding. -/
@[simps! apply symm_apply]
noncomputable
def Spec.homHomeo {R S : CommRingCat}
    [TopologicalSpace R] [ContinuousMul R] [IsLocalRing R]
    [IsOpenUnits R] : (Spec R ⟶ Spec S) ≃ₜ (S ⟶ R) :=
  .symm <| Spec.homEquiv.symm.toHomeomorphOfIsInducing <| by
    have H := isOpenEmbedding_SpecMap_comp_fromSpec R (X := Spec S) ⊤ (isAffineOpen_top _)
    let e := CommRingCat.HomTopology.precompHomeomorph (R := R) (Scheme.ΓSpecIso S)
    convert (H.comp e.isOpenEmbedding).isInducing
    ext1 f
    simp only [homEquiv_symm_apply, Function.comp_apply, Category.assoc, e,
      CommRingCat.HomTopology.precompHomeomorph_apply, map_comp, SpecMap_ΓSpecIso_hom]
    rw [IsAffineOpen.fromSpec_top, ← Scheme.isoSpec_hom,
      Iso.hom_inv_id, Category.comp_id]

lemma IsOpenImmersion.ΓIsoTop_inv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (IsOpenImmersion.ΓIsoTop f).inv = f.appLE _ _ (Set.preimage_range _).ge := by
  simp [IsOpenImmersion.ΓIsoTop, Scheme.Hom.appIso_hom']

variable (R) in
lemma isOpenEmbedding_comp_right
    [TopologicalSpace R] [ContinuousMul R] [IsLocalRing R]
    [IsOpenUnits R] {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] :
    IsOpenEmbedding ((· ≫ f) : (Spec R ⟶ X) → _) := by
  wlog hX : ∃ R, Spec R = X
  · let 𝒰 := X.affineCover
    refine ⟨⟨?_, fun _ _ ↦ (cancel_mono _).mp⟩, ?_⟩
    · rw [isInducing_iff_nhds]
      intro g
      obtain ⟨i, x, hix⟩ := 𝒰.exists_eq (g.base (closedPoint R))
      obtain ⟨g, rfl⟩ : ∃ g' : Spec R ⟶ 𝒰.obj i, g' ≫ 𝒰.map i = g :=
        ⟨_, IsOpenImmersion.lift_fac _ _ ((closedPoint_mem_opensRange _ _).mp
        (by rw [← hix]; exact ⟨_, rfl⟩))⟩
      have this₂ := (this R (𝒰.map i ≫ f) ⟨_, rfl⟩).isInducing
      rw [isInducing_iff_nhds] at this₂
      have this₂ := this₂ g
      apply_fun Filter.map (· ≫ 𝒰.map i) at this₂
      rw [← (this _ _ ⟨_, rfl⟩).map_nhds_eq g, Category.assoc,
        ← (this _ _ ⟨_, rfl⟩).map_nhds_eq g]
      refine (Filter.comap_map (m := (· ≫ f)) fun _ _ ↦ (cancel_mono _).mp).symm.trans ?_
      rw [Filter.map_map]; rfl
    · rw [isOpen_iff_forall_mem_open]
      rintro _ ⟨g, rfl⟩
      obtain ⟨i, x, hix⟩ := 𝒰.exists_eq (g.base (closedPoint R))
      obtain ⟨g, rfl⟩ : ∃ g' : Spec R ⟶ 𝒰.obj i, g' ≫ 𝒰.map i = g :=
        ⟨_, IsOpenImmersion.lift_fac _ _ ((closedPoint_mem_opensRange _ _).mp
        (by rw [← hix]; exact ⟨_, rfl⟩))⟩
      dsimp
      refine ⟨_, ?_, (this R (𝒰.map i ≫ f) ⟨_, rfl⟩).2, ?_⟩
      · exact Set.range_comp_subset_range (· ≫ 𝒰.map i) (· ≫ f)
      · rw [Category.assoc]
        exact ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  let e : Γ(Y, f.opensRange) ≅ S := (IsOpenImmersion.ΓIsoTop f).symm ≪≫ Scheme.ΓSpecIso _
  have := ((isOpenEmbedding_SpecMap_comp_fromSpec R f.opensRange (isAffineOpen_opensRange f)).comp
    (CommRingCat.HomTopology.precompHomeomorph e).isOpenEmbedding).comp
      Spec.homHomeo.isOpenEmbedding
  convert this with g
  suffices g ≫ f = (Spec R).toSpecΓ ≫
      Spec.map (f.appLE f.opensRange ⊤ (Set.preimage_range _).ge ≫ g.appTop) ≫
        (isAffineOpen_opensRange f).fromSpec by
    simpa [e, IsOpenImmersion.ΓIsoTop_inv, Scheme.toSpecΓ_naturality_assoc] using this
  simp only [Scheme.Hom.app_eq_appLE, Scheme.appLE_comp_appLE]
  rw [IsAffineOpen.Spec_map_appLE_fromSpec (V := g ⁻¹ᵁ ⊤) (hV := isAffineOpen_top _),
    IsAffineOpen.fromSpec_top, ← Scheme.isoSpec_hom, Iso.hom_inv_id_assoc]

lemma Scheme.exists_isAffineOpen_and_mem (X : Scheme) (x : X) :
    ∃ U, IsAffineOpen U ∧ x ∈ U := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    (isBasis_affine_open X).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨U, hU, hxU⟩

@[fun_prop]
lemma continuous_comp_right [TopologicalSpace R] [ContinuousMul R] [IsLocalRing R]
    [IsOpenUnits R] (f : X ⟶ Y) :
    Continuous ((· ≫ f) : (Spec R ⟶ X) → _) := by
  rw [continuous_iff_continuousAt]
  intro φ
  obtain ⟨U, hU, hxU⟩ := Y.exists_isAffineOpen_and_mem ((φ ≫ f).base (IsLocalRing.closedPoint R))
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ f ⁻¹ᵁ U⟩ :=
    (isBasis_affine_open X).exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).2
  obtain ⟨φ, rfl⟩ := (range_SpecMap_comp_fromSpec _ hV).ge hxV
  rw [← (isOpenEmbedding_SpecMap_comp_fromSpec (R := R) V hV).continuousAt_iff]
  simp only [Function.comp_def, Category.assoc, ← hU.Spec_map_appLE_fromSpec f hV hVU,
    ← Spec.map_comp_assoc]
  exact ((continuous_SpecMap_comp_fromSpec R U hU).comp
    (CommRingCat.HomTopology.continuous_precomp (f.appLE U V hVU))).continuousAt

@[simps! apply symm_apply]
def homToHomeo [TopologicalSpace R] [ContinuousMul R] [IsLocalRing R]
    [IsOpenUnits R] (f : X ≅ Y) :
    (Spec R ⟶ X) ≃ₜ (Spec R ⟶ Y) where
  __ := f.homToEquiv
  continuous_toFun := continuous_comp_right _
  continuous_invFun := continuous_comp_right _

lemma IsEmbedding.of_comp_iff' {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] (e : α ≃ₜ β) (f : β → γ) :
    IsEmbedding (f ∘ e) ↔ IsEmbedding f :=
  ⟨fun H ↦ by convert H.comp e.symm.isEmbedding; ext; simp, fun H ↦ H.comp e.isEmbedding⟩

@[simp]
lemma coe_ofIsEmbedding_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : IsEmbedding f) (x : X) : (hf.toHomeomorph x).1 = f x := rfl

lemma Scheme.Hom.app_surjective {X Y : Scheme.{u}} (f : X.Hom Y)
    [IsClosedImmersion f] (U : Y.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (f.app U) := by
  have : IsAffine U := hU
  refine ((targetAffineLocally_affineAnd_iff
    (Q := (Function.Surjective ·)) RingHom.surjective_respectsIso f).mp ?_ _ hU).2
  refine (HasAffineProperty.eq_targetAffineLocally (P := @IsClosedImmersion) ..).le _ ‹_›

lemma isEmbedding_comp_right_of_isClosedImmersion
    [TopologicalSpace R] [ContinuousMul R] [IsLocalRing R]
    [IsOpenUnits R] (f : X ⟶ Y) [IsClosedImmersion f] :
    IsEmbedding ((· ≫ f) : (Spec R ⟶ X) → _) := by
  let U (i : Y.affineOpens) : TopologicalSpace.Opens _ :=
      ⟨_, (isOpenEmbedding_SpecMap_comp_fromSpec R i.1 i.2).2⟩
  rw [(TopologicalSpace.IsOpenCover.mk (u := U) ?_).isEmbedding_iff_restrictPreimage]
  · intro U
    unfold Set.restrictPreimage
    dsimp
    have : (Set.range fun g ↦ Spec.map g ≫ (U.2.preimage f).fromSpec) =
        ((· ≫ f) : (Spec R ⟶ X) → _) ⁻¹' Set.range fun g ↦ Spec.map g ≫ U.2.fromSpec := by
      ext;simp [range_SpecMap_comp_fromSpec]; rfl
    let e₁ := (Homeomorph.refl (Spec R ⟶ X)).sets (t := ((· ≫ f) : (Spec R ⟶ X) → _) ⁻¹'
      Set.range fun g ↦ Spec.map g ≫ U.2.fromSpec) this
    let e₂ := (isOpenEmbedding_SpecMap_comp_fromSpec R _ (U.2.preimage f)).isEmbedding.toHomeomorph
    rw [← IsEmbedding.of_comp_iff' (e₂.trans e₁)]
    have := CommRingCat.HomTopology.isEmbedding_precomp_of_surjective
      (R := R) (f.app U) (f.app_surjective _ U.2)
    convert (isOpenEmbedding_SpecMap_comp_fromSpec R _
      U.2).isEmbedding.toHomeomorph.isEmbedding.comp this
    ext g : 2
    simp only [Function.comp_apply, Homeomorph.trans_apply, Set.MapsTo.val_restrict_apply,
      Homeomorph.subtype_apply_coe, coe_ofIsEmbedding_apply, Homeomorph.refl_apply, id_eq,
      Category.assoc, Spec.map_comp, e₂, e₁]
    rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.Spec_map_appLE_fromSpec]
  · exact continuous_comp_right f
  · ext g
    simpa [range_SpecMap_comp_fromSpec, U] using
      Y.exists_isAffineOpen_and_mem (g.base (closedPoint _))

open Limits

lemma isEmbedding_pullback_of_isAffine [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [IsOpenUnits R] {X Y Z : CommRingCat} (f : Spec X ⟶ Spec Z) (g : Spec Y ⟶ Spec Z) :
    IsEmbedding fun i : Spec R ⟶ pullback f g ↦ (i ≫ pullback.fst _ _, i ≫ pullback.snd _ _) := by
  have := isPullback_Spec_map_pushout (Spec.preimage f) (Spec.preimage g)
  simp only [Spec.map_preimage] at this
  convert ((((Spec.homHomeo.prodCongr Spec.homHomeo).symm.isEmbedding).comp
    (CommRingCat.HomTopology.isEmbedding_pushout (R := R)
    (Spec.preimage f) (Spec.preimage g))).comp Spec.homHomeo.isEmbedding).comp
    (homToHomeo this.isoPullback).symm.isEmbedding with φ <;> simp

lemma isEmbedding_pullback [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [IsOpenUnits R] {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsEmbedding fun i : Spec R ⟶ pullback f g ↦ (i ≫ pullback.fst _ _, i ≫ pullback.snd _ _) := by
  let 𝒰₀ := Scheme.Pullback.openCoverOfBase Z.affineCover f g
  let 𝒱 (i : 𝒰₀.J) := ((Z.affineCover.pullbackCover f).obj i).affineCover
  let 𝒲 (i : 𝒰₀.J) := ((Z.affineCover.pullbackCover g).obj i).affineCover
  let 𝒰 : Scheme.OpenCover (pullback f g) := 𝒰₀.bind fun i ↦
    Scheme.Pullback.openCoverOfLeftRight (𝒱 i) (𝒲 i) _ _
  let F (i : 𝒰.J) : (Spec R ⟶ (𝒱 i.1).obj i.2.1) × (Spec R ⟶ (𝒲 i.1).obj i.2.2) →
      (Spec R ⟶ X) × (Spec R ⟶ Y) :=
      Prod.map (· ≫ (𝒱 i.1).map i.2.1 ≫ pullback.fst _ _)
      (· ≫ (𝒲 i.1).map i.2.2 ≫ pullback.fst _ _)
  have hF (i) : IsOpenEmbedding (F i) :=
    .prodMap (isOpenEmbedding_comp_right _ _) (isOpenEmbedding_comp_right _ _)
  refine isEmbedding_of_iSup_eq_top_of_preimage_subset_range _ (by fun_prop)
    (fun i ↦ (⟨_, (hF i).2⟩ : TopologicalSpace.Opens ((Spec R ⟶ X) × (Spec R ⟶ Y)))) ?_
    (fun i ↦ Spec R ⟶ 𝒰.obj i) (fun i ↦ (· ≫ 𝒰.map i)) (by fun_prop) ?_ ?_
  · rintro _ ⟨f₁, rfl⟩
    dsimp
    simp only [Scheme.Pullback.openCoverOfLeftRight_J, Set.range_prodMap,
      TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.coe_mk, Set.mem_iUnion, Set.mem_prod,
      Set.mem_range, F, 𝒰, 𝒱, 𝒲, 𝒰₀]
    obtain ⟨i₁, z₁, e₁⟩ := 𝒰₀.exists_eq (f₁.base (closedPoint _))
    have := (closedPoint_mem_opensRange (f₁ ≫ pullback.fst _ _)
      ((Z.affineCover.pullbackCover f).map i₁)).mp (by
      simp only [Scheme.Cover.pullbackCover_obj, Scheme.Cover.pullbackCover_map,
        Scheme.comp_coeBase, TopCat.comp_app, ← e₁]
      rw [← Scheme.comp_base_apply]
      simp only [Scheme.Pullback.openCoverOfBase_obj, Scheme.Pullback.openCoverOfBase_map,
        limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, 𝒰₀]
      exact ⟨_, rfl⟩)
    let f₂ := IsOpenImmersion.lift _ _ this
    obtain ⟨i₂, z₂, e₂⟩ := (𝒱 i₁).exists_eq (f₂.base (closedPoint _))
    have := (closedPoint_mem_opensRange (f₁ ≫ pullback.snd _ _)
      ((Z.affineCover.pullbackCover g).map i₁)).mp (by
      simp only [Scheme.Cover.pullbackCover_obj, Scheme.Cover.pullbackCover_map,
        Scheme.comp_coeBase, TopCat.comp_app, ← e₁]
      rw [← Scheme.comp_base_apply]
      simp only [Scheme.Pullback.openCoverOfBase_obj, Scheme.Pullback.openCoverOfBase_map,
        limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, 𝒰₀]
      exact ⟨_, rfl⟩)
    let f₃ := IsOpenImmersion.lift _ _ this
    obtain ⟨i₃, z₃, e₃⟩ := (𝒲 i₁).exists_eq (f₃.base (closedPoint _))
    refine ⟨⟨i₁, i₂, i₃⟩, ⟨IsOpenImmersion.lift ((𝒱 i₁).map _) f₂ ?_, ?_⟩,
      IsOpenImmersion.lift ((𝒲 i₁).map _) f₃ ?_, ?_⟩
    · rw [← closedPoint_mem_opensRange]
      exact ⟨_, e₂⟩
    · simp only [𝒱]
      rw [IsOpenImmersion.lift_fac_assoc]
      exact IsOpenImmersion.lift_fac ..
    · rw [← closedPoint_mem_opensRange]
      exact ⟨_, e₃⟩
    · rw [IsOpenImmersion.lift_fac_assoc]
      exact IsOpenImmersion.lift_fac ..
  · rintro i f₁ ⟨⟨f₂, f₃⟩, e⟩
    simp only [Scheme.Pullback.openCoverOfLeftRight_J, Prod.map_apply, Prod.mk.injEq, F] at e
    refine ⟨IsOpenImmersion.lift (𝒰.map i) f₁ ?_, ?_⟩
    · rintro _ ⟨s, rfl⟩
      let a' : Spec R ⟶ 𝒰.obj i := pullback.lift f₂ f₃ (by
        rw [← cancel_mono (Z.affineCover.map _)]
        simp only [Category.assoc, ← pullback.condition, reassoc_of% e.1, reassoc_of% e.2])
      have : a' ≫ 𝒰.map i = f₁ := by
        apply pullback.hom_ext <;>
          -- ↓ lemmas removed for performance reasons
          simp [a', 𝒰, 𝒰₀, e.1, e.2, -eq_mp_eq_cast, -cast_eq, -eq_mpr_eq_cast]
      rw [← this]
      exact ⟨_, rfl⟩
    · simp
  · intro i
    convert (hF i).isEmbedding.comp
      (isEmbedding_pullback_of_isAffine (R := R) ((𝒱 i.1).map i.2.1 ≫ pullback.snd _ _)
      ((𝒲 i.1).map i.2.2 ≫ pullback.snd _ _))
    ext x : 2
    · simp [F, 𝒰, 𝒱, 𝒲, 𝒰₀]
    · simp [F, 𝒰, 𝒱, 𝒲, 𝒰₀]

end AlgebraicGeometry
