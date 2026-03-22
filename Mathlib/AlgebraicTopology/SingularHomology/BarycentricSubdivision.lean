module

public import Mathlib.AlgebraicTopology.SingularHomology.ConvexMetricSpace
public import Mathlib.Analysis.Convex.StdSimplex

@[expose] public section

variable {X : Type*} [ConvexSpace ℝ X] [MetricSpace X] [IsConvexMetricSpace X] [BoundedSpace X]

noncomputable
instance (n) [Fintype n] : ConvexSpace ℝ ↑(stdSimplex ℝ n) :=
  (convex_stdSimplex _ _).convexSpace

noncomputable
instance (n) [Fintype n] : IsConvexMetricSpace ↑(stdSimplex ℝ n) :=
  (convex_stdSimplex _ _).isConvexMetricSpace

noncomputable
instance (n) [Fintype n] : CompactSpace ↑(stdSimplex ℝ n) :=
  isCompact_iff_compactSpace.mp (isCompact_stdSimplex _ _)

noncomputable
instance (n) [Fintype n] : CompactSpace ↑(stdSimplex ℝ n) :=
  isCompact_iff_compactSpace.mp (isCompact_stdSimplex _ _)

noncomputable
instance {T : Type*} [PseudoMetricSpace T] [CompactSpace T] : BoundedSpace T :=
  ⟨(isCompact_iff_totallyBounded_isComplete.mp isCompact_univ).1.isBounded⟩

/-- The projection from `Δₘ₊₁` to `Δₘ` wrt the `0`-th vertex. -/
noncomputable def stdSimplex.proj {m : ℕ}
      (σ : stdSimplex ℝ (Fin (m + 1))) (h : σ 0 ≠ 1) : stdSimplex ℝ (Fin m) :=
  ⟨(1 - σ 0) ⁻¹ • σ ∘ Fin.succ,
  fun i ↦ mul_nonneg (by simp) (by simp), (by
    simpa [← Finset.mul_sum, inv_mul_eq_iff_eq_mul₀, h, sub_eq_iff_eq_add, @eq_comm ℝ 1,
      eq_sub_iff_add_eq', Fin.sum_univ_succ] using σ.prop.right)⟩

lemma stdSimplex.coe_def {𝕜 ι : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [Fintype ι]
    (f : stdSimplex 𝕜 ι) :
    ⇑f = f.val := rfl

@[simp]
lemma stdSimplex.coe_mk {𝕜 ι : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [Fintype ι]
    (f : ι → 𝕜) (hf : f ∈ stdSimplex 𝕜 ι) :
    ⇑(⟨f, hf⟩ : stdSimplex 𝕜 ι) = f := rfl

lemma stdSimplex.convexCombination_apply {ι : Type*} [Fintype ι]
    (f : StdSimplex ℝ ↑(stdSimplex ℝ ι)) (x) :
    ConvexSpace.convexCombination f x = ConvexSpace.convexCombination (f.map (· x)) := by
  rw [stdSimplex.coe_def, Convex.coe_convexCombination, convexCombination_eq_sum]
  simp [StdSimplex.map, Finsupp.sum_mapDomain_index, add_mul, Finsupp.sum_apply',
    convexCombination_eq_sum, stdSimplex.coe_def]

noncomputable def stdSimplex.cone {m : ℕ} (p : X)
      (α : C(stdSimplex ℝ (Fin m), X)) :
    C(stdSimplex ℝ (Fin (m + 1)), X) where
  toFun σ := convexComboPair (σ 0) (1 - σ 0) (by simp) (by simp) (by simp) p
    (if h : σ 0 = 1 then p else α (stdSimplex.proj σ h))
  continuous_toFun := by
    refine continuous_convexComboPair' _ ((continuous_apply _).comp continuous_subtype_val) _
      (by simp) _ _ continuous_const.continuousOn ?_
    rw [continuousOn_iff_continuous_restrict, Set.restrict_eq]
    simp only [Set.preimage_compl, Function.comp_def]
    conv => enter [1, x]; rw [dif_neg (by exact x.2)]
    refine α.2.comp (continuous_induced_rng.mpr (.smul (.inv₀ (.sub continuous_const ?_) ?_) ?_))
    · exact (continuous_apply 0).comp (continuous_subtype_val.comp continuous_subtype_val)
    · simp [sub_eq_zero, @eq_comm ℝ 1]
    · exact (continuous_pi fun i ↦ ((continuous_apply i.succ).comp
        (continuous_subtype_val.comp continuous_subtype_val)))

lemma stdSimplex.cone_apply_of_eq_one {m : ℕ} (p : X)
      (α : C(stdSimplex ℝ (Fin m), X))
      (σ : stdSimplex ℝ (Fin (m + 1))) (H : σ 0 = 1) :
    stdSimplex.cone p α σ = p := by
  simp [H, convexComboPair_one, cone]

lemma stdSimplex.cone_apply {m : ℕ} (p : X)
      (α : C(stdSimplex ℝ (Fin m), X))
      (σ : stdSimplex ℝ (Fin (m + 1))) (σ' : stdSimplex ℝ (Fin m))
      (H : (1 - σ 0) • σ'.1 = σ ∘ Fin.succ) :
    stdSimplex.cone p α σ =
      convexComboPair (σ 0) (1 - σ 0) (by simp) (by simp) (by simp) p (α σ') := by
  by_cases h : σ 0 = 1
  · simp [h, convexComboPair_one, cone_apply_of_eq_one]
  · simp [cone, proj, h, ← H, show 1 - σ 0 ≠ 0 by simpa [sub_eq_zero] using Ne.symm h]

noncomputable def stdSimplex.isAffine_cone {m : ℕ} (p : X)
      (α : C(stdSimplex ℝ (Fin m), X)) (H : ConvexSpace.IsAffine ℝ α) :
    ConvexSpace.IsAffine ℝ (cone p α) := by
  refine ⟨fun s ↦ ?_⟩
  dsimp [cone, convexComboPair]
  rw [← StdSimplex.map_map, ConvexSpace.assoc]
  sorry

noncomputable def stdSimplex.isAffine_map {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y) :
    ConvexSpace.IsAffine ℝ (stdSimplex.map (S := ℝ) f) := by
  refine ⟨fun s ↦ ?_⟩
  sorry
