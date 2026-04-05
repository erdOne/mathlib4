module

public import Mathlib.AlgebraicTopology.SingularHomology.BarycentricSubdivision
public import Mathlib.Topology.Sets.OpenCover

@[expose] public section


attribute [simp] Finsupp.support_single_ne_zero

namespace Convexity.StdSimplex

variable (𝕜 ι : Type*) [Semifield 𝕜] [PartialOrder 𝕜] [PosMulReflectLT 𝕜] [IsOrderedRing 𝕜]
  [Fintype ι] [CharZero 𝕜] [Nonempty ι]

@[simps]
def barycenter : StdSimplex 𝕜 ι where
  weights.support := .univ
  weights.toFun _ := (Fintype.card ι : 𝕜)⁻¹
  weights.mem_support_toFun _ := by simp
  nonneg _ := by simp
  total := by simp [Finsupp.sum]

end Convexity.StdSimplex

namespace Convexity

variable {R M N I J : Type*} [PartialOrder R] [CommSemiring R] [IsStrictOrderedRing R]
  [ConvexSpace R M] [ConvexSpace R N] --{s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1)

-- TODO: connect to `IsConvex`
variable (R) in
def IsConvex (s : Set M) : Prop := ∀ f : StdSimplex R M, ↑f.weights.support ⊆ s → f.sConvexCombo ∈ s

lemma IsConvex.sConvexCombo_mem {s : Set M} (hs : IsConvex R s) (f : StdSimplex R M)
    (hf : ↑f.weights.support ⊆ s) : f.sConvexCombo ∈ s := hs _ hf

lemma IsConvex.iConvexCombo_mem {s : Set M} (hs : IsConvex R s) (f : StdSimplex R I)
    (g : I → M) (hg : Set.MapsTo g ↑f.weights.support s) : f.iConvexCombo g ∈ s := by
  classical exact hs _ ((Finset.coe_subset.mpr Finsupp.mapDomain_support).trans (by simpa))

lemma IsConvex.convexComboPair_mem {s : Set M} (hs : IsConvex R s)
    {t₁ t₂ : R} (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) (h : t₁ + t₂ = 1)
    {x y : M} (hx : x ∈ s) (hy : y ∈ s) : convexComboPair t₁ t₂ ht₁ ht₂ h x y ∈ s := by
  classical exact hs _ ((Finset.coe_subset.mpr Finsupp.support_add).trans <| by grind)

lemma IsConvex.univ : IsConvex R (Set.univ : Set M) := by simp [IsConvex]

lemma IsConvex.inter {s t : Set M} (hs : IsConvex R s) (ht : IsConvex R t) :
    IsConvex R (s ∩ t) := by simp_all [IsConvex]

lemma IsConvex.sInter {S : Set (Set M)} (hs : ∀ s ∈ S, IsConvex R s) :
    IsConvex R (⋂₀ S) := by simp_all [IsConvex]

lemma IsConvex.iInter {s : I → Set M} (hs : ∀ i, IsConvex R (s i)) :
    IsConvex R (⋂ i, s i) := by simp_all [IsConvex]

@[simp]
lemma StdSimplex.weights_ne_zero (f : StdSimplex R I) : f.weights ≠ 0 :=
  fun h ↦ by simpa [h] using f.total

-- lemma Finsupp.range_mapDomain {α β M : Type*} [AddCommMonoid M] (f : α → β) :
--     Set.range (Finsupp.mapDomain (M := M) f) = { σ | σ.support ⊆ Set.range f } := by
--   classical
--   refine (Set.range_subset_iff.mpr fun x ↦ ?_).antisymm fun σ hσ ↦ ?_
--   · dsimp; grw [Finsupp.mapDomain_support]; simp
--   cases isEmpty_or_nonempty α
--   · obtain rfl : σ = 0 := by simpa [Set.range_eq_empty] using hσ
--     exact ⟨0, by simp⟩
--   refine ⟨σ.mapDomain (Function.invFun f), ?_⟩
--   rw [← Finsupp.mapDomain_comp, Finsupp.mapDomain_congr (g := id), Finsupp.mapDomain_id]
--   simp_all [Function.invFun_eq, Set.subset_def]

lemma StdSimplex.range_map (f : I → J) :
    Set.range (StdSimplex.map (R := R) f) = { σ | σ.weights.support ⊆ Set.range f } := by
  classical
  refine (Set.range_subset_iff.mpr fun x ↦ ?_).antisymm fun σ hσ ↦ ?_
  · dsimp; grw [Finsupp.mapDomain_support]; simp
  cases isEmpty_or_nonempty I
  · simp [Set.range_eq_empty] at hσ
  refine ⟨σ.map (Function.invFun f), ext ?_⟩
  dsimp
  rw [← Finsupp.mapDomain_comp, Finsupp.mapDomain_congr (g := id), Finsupp.mapDomain_id]
  simp_all [Function.invFun_eq, Set.subset_def]

lemma IsConvex.empty : IsConvex R (∅ : Set M) := by simp [IsConvex]

lemma IsConvex.image {s : Set M} (hs : IsConvex R s) {f : M → N} (hf : IsAffineMap R f) :
    IsConvex R (f '' s) := by
  classical
  intro α hα
  rw [← Subtype.range_coe (s := s), ← Set.range_comp] at hα
  obtain ⟨α, rfl⟩ := (StdSimplex.range_map _).ge hα
  rw [StdSimplex.map_comp, ← hf.map_sConvexCombo]
  exact ⟨_, hs.iConvexCombo_mem _ _ fun _ ↦ by simp, rfl⟩

lemma IsAffineMap.isConvex_range {f : M → N} (hf : IsAffineMap R f) :
    IsConvex R (Set.range f) := by
  simpa using IsConvex.univ.image hf

end Convexity

@[simp]
lemma Fin.castSucc_eq_zero {n} {i : Fin n} : i.castSucc = 0 ↔ i.1 = 0 := by
  simp [← Fin.val_eq_zero_iff]

@[simp]
lemma Fin.succAbove_eq_zero {n} {i : Fin (n + 1)} {j : Fin n} :
    i.succAbove j = 0 ↔ i ≠ 0 ∧ j.1 = 0 := by
  delta Fin.succAbove
  split_ifs
  · simp; grind
  · simp_all [Fin.le_iff_val_le_val]; grind

lemma Fin.succAbove_eq_iff {n} {i k : Fin (n + 1)} {j : Fin n} :
    i.succAbove j = k ↔ if i.1 ≤ j.1 then j.1 + 1 = k.1 else j.1 = k.1 := by
  delta Fin.succAbove; grind [Fin.lt_def]

open Convexity

namespace AlgebraicTopology

set_option backward.isDefEq.respectTransparency false

universe w v u

@[simp]
lemma stdSimplex.coe_apply (𝕜 ι : Type*) [Semiring 𝕜] [PartialOrder 𝕜] [Fintype ι]
    (σ : stdSimplex 𝕜 ι) (i : ι) : σ.1 i = σ i := rfl

@[simp]
lemma stdSimplex.mk_apply (𝕜 ι : Type*) [Semiring 𝕜] [PartialOrder 𝕜] [Fintype ι]
    (σ) (hσ : σ ∈ stdSimplex 𝕜 ι) (i : ι) :
  (Subtype.mk σ hσ) i = σ i := rfl

section
variable (𝕜 ι : Type*) [Field 𝕜] [PartialOrder 𝕜]
  [PosMulReflectLT 𝕜] [IsOrderedRing 𝕜] [Fintype ι] [CharZero 𝕜] [Nonempty ι]

@[simps]
def stdSimplex.barycenter : stdSimplex 𝕜 ι := ⟨fun _ ↦ (Fintype.card ι : 𝕜)⁻¹, by simp, by simp⟩

variable [DecidableEq ι]

lemma stdSimplex.iConvexCombo_barycenter :
    StdSimplex.iConvexCombo (.barycenter ℝ ι) stdSimplex.vertex = stdSimplex.barycenter ℝ ι := by
  ext
  simp [StdSimplex.iConvexCombo, StdSimplex.barycenter, stdSimplex.barycenter, -coe_apply,
    stdSimplex.coe_def, sConvexCombo_eq_sum, StdSimplex.map, add_smul,
    Finsupp.sum_mapDomain_index, Finsupp.sum_fintype, Pi.single_apply]

variable {X : Type*}

open stdSimplex StdSimplex

lemma dist_barycenter_left_le (x : stdSimplex ℝ ι) :
    dist (stdSimplex.barycenter ℝ ι) x ≤
      ∑ i, (Fintype.card ι : ℝ)⁻¹ * dist (stdSimplex.vertex i) x := by
  simpa [← iConvexCombo_barycenter] using dist_iConvexCombo_left_le ..

lemma dist_barycenter_right_le (x : stdSimplex ℝ ι) :
    dist x (stdSimplex.barycenter ℝ ι) ≤
      ∑ i, (Fintype.card ι : ℝ)⁻¹ * dist x (stdSimplex.vertex i) := by
  simpa [← iConvexCombo_barycenter] using dist_iConvexCombo_right_le ..

end

variable {m n : ℕ}

variable {C} (R : C)

attribute [-simp] stdSimplex.map_coe

section foo

variable {M : Type*} [AddCommGroup M] {X : Type u} [MetricSpace X]

noncomputable
def boundary {X : Type*} [TopologicalSpace X] {n : ℕ} :
    (C(stdSimplex ℝ (Fin (n + 1)), X) →₀ M) →+ (C(stdSimplex ℝ (Fin n), X) →₀ M) :=
  Finsupp.liftAddHom fun σ ↦ ∑ i : Fin (n + 1),
    (-1) ^ i.1 • Finsupp.singleAddHom (σ.comp ⟨_, stdSimplex.continuous_map (Fin.succAbove i)⟩)

noncomputable
def diam (σ : C(stdSimplex ℝ (Fin n), X) →₀ M) : NNReal :=
  σ.support.sup fun α ↦ Finset.univ.sup fun ij : Fin n × Fin n ↦
    nndist (α (stdSimplex.vertex ij.1)) (α (stdSimplex.vertex ij.2))

lemma nndist_le_diam {σ : C(stdSimplex ℝ (Fin n), X) →₀ M} {α : C(stdSimplex ℝ (Fin n), X)}
    (hα : α ∈ σ.support) {i j : Fin n} :
    nndist (α (stdSimplex.vertex i)) (α (stdSimplex.vertex j)) ≤ diam σ :=
  Finset.le_sup_of_le hα <| Finset.le_sup_of_le (Finset.mem_univ (i, j)) le_rfl

@[simp] lemma diam_zero : diam (0 : C(stdSimplex ℝ (Fin n), X) →₀ M) = 0 := by simp [diam]

lemma diam_add_le (σ τ : C(stdSimplex ℝ (Fin n), X) →₀ M) : diam (σ + τ) ≤ diam σ ⊔ diam τ := by
  classical unfold diam; grw [Finsupp.support_add, Finset.sup_union]

lemma diam_add {σ τ : C(stdSimplex ℝ (Fin n), X) →₀ M} (h : Disjoint σ.support τ.support) :
    diam (σ + τ) = diam σ ⊔ diam τ := by
  classical unfold diam; rw [Finsupp.support_add_eq h, Finset.sup_union]

lemma diam_sum_le {ι : Type*} (s : Finset ι) (f : ι → C(stdSimplex ℝ (Fin n), X) →₀ M) :
    diam (∑ i ∈ s, f i) ≤ s.sup fun i ↦ diam (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s has IH =>
    simp only [has, not_false_eq_true, Finset.sum_insert, Finset.sup_insert]
    grw [diam_add_le, IH]

lemma diam_finsuppSum_le {ι α : Type*} [Zero α]
    (f : ι →₀ α) (g : ι → α → C(stdSimplex ℝ (Fin n), X) →₀ M) :
    diam (f.sum g) ≤ f.support.sup fun i ↦ diam (g i (f i)) :=
  diam_sum_le ..

lemma diam_boundary_le (σ : C(stdSimplex ℝ (Fin (n + 1)), X) →₀ M) :
    diam (boundary σ) ≤ diam σ := by
  classical
  simp only [boundary, Int.reduceNeg, Finsupp.liftAddHom_apply]
  grw [diam_finsuppSum_le]
  refine Finset.sup_le_iff.mpr fun α hα ↦ ?_
  rw [Finsupp.mem_support_iff] at hα
  simp only [Int.reduceNeg, AddMonoidHom.finset_sum_apply, AddMonoidHom.smul_apply,
    Finsupp.singleAddHom_apply, Finsupp.smul_single]
  grw [diam_sum_le]
  refine Finset.sup_le_iff.mpr fun i _ ↦ ?_
  rw [diam]
  simp [Finsupp.single_apply, IsUnit.smul_eq_zero, IsUnit.pow, hα, nndist_le_diam]

variable [ConvexSpace ℝ X] [ConvexSpace.IsMetricCompatible X] [BoundedSpace X]

noncomputable
def bary : ∀ ⦃n⦄,
    (C(stdSimplex ℝ (Fin n), X) →₀ M) →+ (C(stdSimplex ℝ (Fin n), X) →₀ M) :=
  Nat.rec (.id _) fun _ α ↦ Finsupp.liftAddHom fun σ ↦
    .comp (.comp (.comp (Finsupp.lmapDomain _ ℤ (stdSimplex.cone
      (σ (stdSimplex.barycenter _ _)))).toAddMonoidHom α) boundary) (Finsupp.singleAddHom σ)

lemma bary_succ : bary (X := X) (M := M) (n := n + 1) = Finsupp.liftAddHom fun σ ↦
    .comp (.comp (.comp (Finsupp.lmapDomain _ ℤ (stdSimplex.cone
      (σ (stdSimplex.barycenter _ _)))).toAddMonoidHom (bary (n := n))) boundary)
      (Finsupp.singleAddHom σ) := rfl

lemma diam_cone (p : X) (α : C(stdSimplex ℝ (Fin n), X)) {m : M} (hm : m ≠ 0) :
    diam (Finsupp.single (stdSimplex.cone p α) m) =
      Finset.univ.sup (fun i ↦ nndist (α <| stdSimplex.vertex i) p) ⊔
        diam (Finsupp.single α m) := by
  simp only [diam, ne_eq, hm, not_false_eq_true, Finsupp.support_single_ne_zero,
    Finset.sup_singleton]
  rw [← Finset.univ_product_univ, Fin.univ_succ]
  simp only [Finset.cons_eq_insert, ← Finset.union_singleton, Finset.product_union,
    Finset.union_product, ← Finset.prodMap_map_product, Finset.sup_union]
  simp [Function.comp_def, nndist_comm p, max_comm]

lemma diam_mapDomain_cone (p : X) (σ : C(stdSimplex ℝ (Fin n), X) →₀ M) :
    diam (σ.mapDomain (stdSimplex.cone p)) ≤
      σ.support.sup (fun α ↦ Finset.univ.sup (fun i ↦ nndist (α <| stdSimplex.vertex i) p)) ⊔
        diam σ := by
  induction σ using Finsupp.induction with
  | zero => simp
  | single_add a b f ha hb IH =>
  simp only [Finsupp.mapDomain_add, Finsupp.mapDomain_single, ha, not_false_eq_true, ne_eq, hb,
    Finsupp.support_single_add, Finset.sup_cons]
  grw [diam_add_le, IH, diam_cone (hm := hb), diam_add (by simp [*]), sup_sup_sup_comm]

instance {I : Type*} [IsEmpty I] [Fintype I] : IsEmpty (stdSimplex ℝ I) :=
  ⟨fun f ↦ by simpa using f.2.2⟩

abbrev IsGeometric (σ : C(stdSimplex ℝ (Fin n), X) →₀ M) : Prop :=
  ∀ β ∈ σ.support, IsAffineMap ℝ β

omit [ConvexSpace.IsMetricCompatible X] [BoundedSpace X] in
lemma IsGeometric.single {σ : C(stdSimplex ℝ (Fin (n + 1)), X) →₀ M} (hσ : IsGeometric σ)
    (β : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    IsGeometric (.single β (σ β)) := by
  classical grind

omit [ConvexSpace ℝ X] [ConvexSpace.IsMetricCompatible X] [BoundedSpace X] in
lemma exists_eq_comp_of_mem_support_boundary
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X) →₀ M)
    (α : C(stdSimplex ℝ (Fin n), X)) (hα : α ∈ (boundary σ).support) :
    ∃ β ∈ σ.support, ∃ i : Fin (n + 1), α = β.comp ⟨_, stdSimplex.continuous_map i.succAbove⟩ := by
  classical
  dsimp [boundary] at hα
  grw [Finsupp.support_sum, Finset.mem_biUnion] at hα
  obtain ⟨β, hβ, h⟩ := hα
  rw [Finsupp.mem_support_iff] at hβ
  grw [AddMonoidHom.finset_sum_apply, Finsupp.support_finset_sum, Finset.mem_biUnion] at h
  obtain ⟨i, -, h⟩ := h
  refine ⟨β, by simpa, i, .symm ?_⟩
  simpa [Finsupp.single_apply, IsUnit.smul_eq_zero, IsUnit.pow, hβ] using h

omit [ConvexSpace.IsMetricCompatible X] [BoundedSpace X] in
lemma IsGeometric.boundary {σ : C(stdSimplex ℝ (Fin (n + 1)), X) →₀ M} (hσ : IsGeometric σ) :
    IsGeometric (boundary σ) := by
  intro α hα
  obtain ⟨β, hβ, i, rfl⟩ := exists_eq_comp_of_mem_support_boundary σ α hα
  exact (hσ β hβ).comp (stdSimplex.isAffineMap_map _)

lemma exists_range_subset_of_mem_support_bary
    (σ : C(stdSimplex ℝ (Fin n), X) →₀ M) (hσ : IsGeometric σ)
    (α : C(stdSimplex ℝ (Fin n), X)) (hα : α ∈ (bary σ).support) :
    ∃ β ∈ σ.support, Set.range α ⊆ Set.range β := by
  classical
  induction n with
  | zero => simp_all [bary, Set.range_eq_empty]; grind
  | succ n IH =>
  dsimp [bary_succ] at hα
  simp only [Finsupp.mem_support_iff, Finsupp.sum_apply] at hα
  obtain ⟨β, hβ, h⟩ := not_forall₂.mp (mt Finset.sum_eq_zero hα)
  simp only [Finsupp.mem_support_iff] at hβ
  replace h : (bary (boundary (Finsupp.single β (σ β)))).mapDomain
      (stdSimplex.cone (β (stdSimplex.barycenter ℝ _))) α ≠ 0 := by
    simpa using h
  simp only [Finsupp.mapDomain, Finsupp.sum_apply, ne_eq] at h
  obtain ⟨γ, hγ, h'⟩ := not_forall₂.mp (mt Finset.sum_eq_zero h)
  simp only [Finsupp.single_apply, ite_eq_right_iff, Classical.not_imp] at h'
  obtain ⟨rfl, -⟩ := h'
  clear h hα
  obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), Set.range γ ⊆ Set.range (β ∘ stdSimplex.map i.succAbove) := by
    have := IH _ (.boundary (.single hσ _)) _ hγ
    dsimp [boundary] at this
    grw [Finsupp.sum_single_index (by simp), AddMonoidHom.finset_sum_apply,
      Finsupp.support_finset_sum] at this
    simpa [Finsupp.single_apply, IsUnit.smul_eq_zero, IsUnit.pow, hβ] using this
  refine ⟨β, by simpa, ?_⟩
  rintro _ ⟨x, rfl⟩
  refine (hσ β (by simpa)).isConvex_range.convexComboPair_mem _ _ _ (by simp) ?_
  split_ifs with h; · simp
  exact hi.trans (Set.range_comp_subset_range ..) (by simp)

noncomputable
def stdSimplex.equivStdSimplex {I : Type*} [Fintype I] [DecidableEq I] :
    StdSimplex ℝ I ≃ stdSimplex ℝ I where
  toFun σ := ⟨σ.weights, σ.nonneg, by simpa [Finsupp.sum_fintype] using σ.total⟩
  invFun σ := ⟨Finsupp.equivFunOnFinite.symm σ.1, fun i ↦ by simp, by simp [Finsupp.sum_fintype]⟩
  left_inv σ := StdSimplex.ext (by simp)
  right_inv σ := Subtype.ext (by simp)

lemma stdSimplex.iConvexCombo_vertex_bijective {I : Type*} [Fintype I] [DecidableEq I] :
    Function.Bijective fun f ↦ iConvexCombo (R := ℝ) f (stdSimplex.vertex (S := ℝ) (X := I)) := by
  convert stdSimplex.equivStdSimplex (I := I).bijective with f
  ext i
  simp [← stdSimplex.coe_apply, iConvexCombo_eq_sum, Finsupp.sum, Pi.single_apply,
    equivStdSimplex, eq_comm]

lemma diam_bary_single_le (α : C(stdSimplex ℝ (Fin (n + 1)), X)) {m : M} (hm : m ≠ 0)
    (H : IsGeometric (Finsupp.single α m)) :
    diam (bary (.single α m)) ≤
      Finset.univ.sup
        (fun i ↦ nndist (α <| stdSimplex.vertex i) (α <| stdSimplex.barycenter ..)) ⊔
        diam (bary (boundary (.single α m))) := by
  classical
  dsimp [bary_succ]
  rw [Finsupp.sum_single_index (by simp)]
  dsimp
  grw [diam_mapDomain_cone]
  gcongr
  simp only [Finset.sup_le_iff, Finsupp.mem_support_iff, ne_eq, Finset.mem_univ, forall_const]
  intro β hβ i
  generalize α (stdSimplex.barycenter ℝ (Fin (n + 1))) = p
  obtain ⟨γ, hγ, h⟩ :=
    exists_range_subset_of_mem_support_bary _ (.boundary H) _ (Finsupp.mem_support_iff.mpr hβ)
  obtain ⟨γ, hγ', j, rfl⟩ := exists_eq_comp_of_mem_support_boundary _ _ hγ
  obtain rfl : γ = α := by simpa [Finsupp.single_apply, hm] using hγ'
  have : Set.range β ⊆ Set.range (γ ∘ fun f ↦ iConvexCombo (R := ℝ) f stdSimplex.vertex) := by
    grw [Set.range_comp, Set.range_eq_univ.mpr stdSimplex.iConvexCombo_vertex_bijective.2,
      Set.image_univ, h, ContinuousMap.coe_comp, Set.range_comp_subset_range]
  have ⟨x, hx⟩ := this (Set.mem_range_self (stdSimplex.vertex i))
  simp only [← hx, Function.comp_apply, (H γ (by simpa)).map_iConvexCombo]
  grw [nndist_iConvexCombo_left_le_sup, Finset.sup_mono (Finset.subset_univ _)]
  rfl

lemma diam_bary_le_diam (σ : C(stdSimplex ℝ (Fin n), X) →₀ M) (hσ : IsGeometric σ) :
    diam (bary σ) ≤ ((n - 1) / n) * diam σ := by
  induction n with
  | zero => simp [bary, diam, ← bot_eq_zero (α := NNReal), -bot_eq_zero']
  | succ n ihn =>
  induction σ using Finsupp.induction with
  | zero => simp
  | single_add α m σ hα hm ihσ =>
  classical
  rw [IsGeometric, Finsupp.support_add_eq (by simp [*])] at hσ
  simp only [hm, or_imp, not_false_eq_true, Finsupp.support_single_ne_zero, Finset.singleton_union,
    Finset.mem_insert, Finsupp.mem_support_iff, ne_eq, forall_and, forall_eq, IsGeometric] at hσ ihσ
  grw [map_add, diam_add_le, diam_add (by simp [*]), mul_max, diam_bary_single_le _ hm
    (by simp [IsGeometric, Finsupp.single_apply, hσ.1]), ihn, ihσ hσ.2, diam_boundary_le]
  · gcongr
    simp only [Nat.cast_add, Nat.cast_one, sup_le_iff, Finset.sup_le_iff, Finset.mem_univ,
      forall_const]
    refine ⟨fun i ↦ ?_, by cases n; (· simp); gcongr ?_ * _; field_simp; simp [mul_add, add_mul]⟩
    grw [← stdSimplex.iConvexCombo_barycenter, hσ.1.map_iConvexCombo, nndist_iConvexCombo_right_le]
    simp [Finsupp.sum, Real.toNNReal_inv, ← Finset.mul_sum]
    field_simp
    grw [← Finset.sum_erase _ (a := i) (by simp)]
    convert Finset.sum_le_card_nsmul _ _ (diam <| .single α m) fun i _ ↦ ?_ using 1
    · simp
    · exact nndist_le_diam (by simpa)
  · dsimp [boundary]
    rw [Finsupp.sum_single_index (by simp), AddMonoidHom.finset_sum_apply]
    refine fun β ↦ ?_ ∘ (Finsupp.support_finset_sum ·)
    revert β
    simp [Finsupp.single_apply, ← @forall_comm (Fin _), hσ.1.comp (stdSimplex.isAffineMap_map _)]

open TopologicalSpace Topology

def SubordinateTo {ι : Type*} (σ : C(stdSimplex ℝ (Fin n), X) →₀ M) (U : ι → Opens X) :=
  ∀ α ∈ σ.support, ∃ i, Set.range α ⊆ U i

lemma foo (σ : C(stdSimplex ℝ (Fin n), X) →₀ M) {ι : Type*} {U : ι → Opens X}
    (hU : IsOpenCover U) : ∃ i, SubordinateTo ((bary (n := n))^[i] σ) U := by

  sorry

end foo

end AlgebraicTopology
