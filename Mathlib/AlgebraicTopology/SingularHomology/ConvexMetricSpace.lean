module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.ConvexSpace.AffineSpace

@[expose] public section

variable {X : Type*} [ConvexSpace ℝ X] [MetricSpace X]

open ConvexSpace

variable (X) in
class IsConvexMetricSpace : Prop where
  dist_convexCombination_map_le' (f : StdSimplex ℝ ℕ) (σ₁ σ₂ : ℕ → X) :
    dist (convexCombination (f.map σ₁)) (convexCombination (f.map σ₂)) ≤
      f.weights.sum fun i r ↦ r * dist (σ₁ i) (σ₂ i)

lemma StdSimplex.nonempty {R M : Type*} [PartialOrder R] [Semiring R] [LE R] [Nontrivial R]
    (f : StdSimplex R M) : Nonempty M := by
  by_contra!
  simpa [Subsingleton.elim f.weights 0, -total] using f.total

lemma dist_convexCombination_map_le [IsConvexMetricSpace X] {ι : Type*}
    (f : StdSimplex ℝ ι) (σ₁ σ₂ : ι → X) :
    dist (convexCombination (f.map σ₁)) (convexCombination (f.map σ₂)) ≤
      f.weights.sum fun i r ↦ r * dist (σ₁ i) (σ₂ i) := by
  classical
  let e : ι → ℕ := Function.extend (↑) (f.support.equivFin ·) 0
  have he (x : _) (hx : x ∈ f.support) : e x = ↑(f.support.equivFin ⟨x, hx⟩) :=
      Function.Injective.extend_apply Subtype.val_injective _ _ ⟨x, hx⟩
  let einv : ℕ → ι := Function.extend (↑) (f.support.equivFin.symm ·) (fun _ ↦ f.nonempty.some)
  have H (x : _) (hx : x ∈ f.support) : einv (e x) = x := by simp [he, hx, einv, Fin.val_injective]
  convert IsConvexMetricSpace.dist_convexCombination_map_le' (f.map e) (σ₁ ∘ einv) (σ₂ ∘ einv)
    using 3
  · ext1
    simp only [StdSimplex.map, ← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_congr fun x hx ↦ by simp [H, hx]
  · ext1
    simp only [StdSimplex.map, ← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_congr fun x hx ↦ by simp [H, hx]
  · simp only [StdSimplex.map, Function.comp_apply, zero_mul, implies_true, add_mul,
      Finsupp.sum_mapDomain_index]
    exact Finsupp.sum_congr fun x hx ↦ by simp [H, hx]

@[simp]
lemma StdSimplex.map_const {R M N : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
    (f : StdSimplex R M) (x : N) : f.map (fun _ ↦ x) = .single x := by
  classical
  ext a
  suffices (f.sum fun a₁ b ↦ if x = a then b else 0) = if x = a then 1 else 0 by
    simpa [StdSimplex.map, Finsupp.mapDomain, ← mk_single, Finsupp.single_apply]
  split_ifs <;> simp

@[simp]
lemma StdSimplex.map_id {R M : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
    (f : StdSimplex R M) : f.map id = f := by
  ext; simp [map]

lemma StdSimplex.map_comp {R M N P : Type*}
    [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
    (f : StdSimplex R M) (g₁ : M → N) (g₂ : N → P) : f.map (g₂ ∘ g₁) = (f.map g₁).map g₂ := by
  ext; simp [map, Finsupp.mapDomain_comp]

lemma StdSimplex.map_map {R M N P : Type*}
    [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
    (f : StdSimplex R M) (g₁ : M → N) (g₂ : N → P) :
    (f.map g₁).map g₂ = f.map (fun x ↦ g₂ (g₁ x)) :=
  (StdSimplex.map_comp ..).symm

lemma dist_convexCombination_left [IsConvexMetricSpace X] (f : StdSimplex ℝ X) (x : X) :
    dist (convexCombination f) x ≤ f.weights.sum fun i r ↦ r * dist i x := by
  simpa using dist_convexCombination_map_le f id (fun _ ↦ x)

lemma dist_convexCombination_right [IsConvexMetricSpace X] (f : StdSimplex ℝ X) (x : X) :
    dist x (convexCombination f) ≤ f.weights.sum fun i r ↦ r * dist x i := by
  simpa using dist_convexCombination_map_le f (fun _ ↦ x) id

noncomputable
instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] : ConvexSpace ℝ E := inferInstance

lemma convexCombination_eq_sum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : StdSimplex ℝ E) :
    convexCombination f = f.sum fun i r ↦ r • i := by
  simp [AddTorsor.convexCombination_eq_affineCombination,
    Finset.affineCombination_eq_linear_combination _ _ _ f.total, Finsupp.sum]

noncomputable
def Convex.convexSpace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (S : Set E) (H : Convex ℝ S) :
    ConvexSpace ℝ S where
  convexCombination f := ⟨convexCombination (f.map (↑)), by
    simpa [convexCombination_eq_sum, StdSimplex.map, Finsupp.sum_mapDomain_index, add_smul] using
      H.sum_mem (fun _ _ ↦ f.nonneg _) f.total fun i _ ↦ i.2⟩
  assoc f := by
    simp [convexCombination_eq_sum, StdSimplex.map, Finsupp.sum_mapDomain_index, add_smul,
      StdSimplex.join, Finsupp.sum_sum_index, Finsupp.sum_smul_index, mul_smul, Finsupp.smul_sum]
  single x := by simp [convexCombination_eq_sum, ← StdSimplex.mk_single, StdSimplex.map]

@[simp]
lemma Convex.coe_convexCombination {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (S : Set E) (H : Convex ℝ S) (f : StdSimplex ℝ S) :
    letI := H.convexSpace; (↑(convexCombination f) : E) = convexCombination (f.map (↑)) :=
  rfl

instance (priority := low) {V : Type*} {P : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] :
    IsConvexMetricSpace P where
  dist_convexCombination_map_le' f σ₁ σ₂ := by
    let p : P := Nonempty.some inferInstance
    simp only [AddTorsor.convexCombination_eq_affineCombination, ge_iff_le]
    rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ (f.map σ₁).total p,
      Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ (f.map σ₂).total p]
    trans ‖((StdSimplex.map σ₁ f).sum fun x i ↦ i • (x -ᵥ p)) -
      (StdSimplex.map σ₂ f).sum fun x i ↦ i • (x -ᵥ p)‖
    · simp [dist_eq_norm_vsub, Finsupp.sum]
    trans ‖f.sum fun a b ↦ b • (σ₁ a -ᵥ σ₂ a)‖
    · simp [StdSimplex.map, Finsupp.sum_mapDomain_index, add_smul, ← Finsupp.sum_sub, ← smul_sub]
    grw [Finsupp.sum, Finsupp.sum, norm_sum_le]
    simp [norm_smul, abs_eq_self.mpr (f.nonneg _), dist_eq_norm_vsub]

lemma Convex.isConvexMetricSpace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (S : Set E) (H : Convex ℝ S) :
    letI := H.convexSpace
    IsConvexMetricSpace S := by
  let := H.convexSpace
  refine ⟨fun f σ₁ σ₂ ↦ .trans ?_ (dist_convexCombination_map_le (X := E) f (σ₁ ·) (σ₂ ·))⟩
  simp [Subtype.dist_eq, StdSimplex.map_map]
#min_imports
