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

noncomputable def stdSimplex.cone {m : ℕ} (p : X)
      (α : C(stdSimplex ℝ (Fin m), X)) :
    C(stdSimplex ℝ (Fin (m + 1)), X) where
  toFun σ := convexComboPair (σ 0) (1 - σ 0) (by simp) (by simp) (by simp) p
    (if h : σ 0 = 1 then p else α ⟨(1 - σ 0) ⁻¹ • σ ∘ Fin.succ,
    fun i ↦ mul_nonneg (by simp) (by simp), (by
      simpa [← Finset.mul_sum, inv_mul_eq_iff_eq_mul₀, h, sub_eq_iff_eq_add, @eq_comm ℝ 1,
        eq_sub_iff_add_eq', Fin.sum_univ_succ] using σ.prop.right)⟩)
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
  · simp [cone, h, ← H, show 1 - σ 0 ≠ 0 by simpa [sub_eq_zero] using Ne.symm h]
