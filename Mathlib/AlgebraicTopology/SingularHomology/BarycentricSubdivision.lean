module

public import Mathlib.Analysis.Convex.MetricSpace
public import Mathlib.Analysis.Convex.StdSimplex

@[expose] public section

lemma Finsupp.mapDomain_sum' {α β γ M N : Type*}
    [AddCommMonoid M] [Zero N] {f : α → β} {s : γ →₀ N} {v : γ → N → α →₀ M} :
    mapDomain f (s.sum v) = s.sum fun a b ↦ mapDomain f (v a b) :=
  map_finsuppSum (mapDomain.addMonoidHom f : (α →₀ M) →+ β →₀ M) _ _

namespace Convexity

variable {R E I J M N : Type*} [PartialOrder R] [CommRing R]
    [IsStrictOrderedRing R] [ConvexSpace R M] [ConvexSpace R N] [AddCommGroup E] [Module R E]

variable {X : Type*} [ConvexSpace ℝ X] [MetricSpace X] [ConvexSpace.IsMetricCompatible X]
  [BoundedSpace X]

noncomputable
instance (n) [Fintype n] : ConvexSpace ℝ ↑(stdSimplex ℝ n) := .ofConvex (convex_stdSimplex ..)

instance (n) [Fintype n] : ConvexSpace.IsMetricCompatible ↑(stdSimplex ℝ n) :=
  .of_convex (convex_stdSimplex ..)

open ConvexSpace

lemma stdSimplex.coe_def {𝕜 ι : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [Fintype ι]
    (f : stdSimplex 𝕜 ι) :
    ⇑f = f.val := rfl

@[simp]
lemma stdSimplex.coe_mk {𝕜 ι : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [Fintype ι]
    (f : ι → 𝕜) (hf : f ∈ stdSimplex 𝕜 ι) :
    ⇑(⟨f, hf⟩ : stdSimplex 𝕜 ι) = f := rfl

/-- The projection from `Δₘ₊₁` to `Δₘ` wrt the `0`-th vertex. -/
noncomputable def stdSimplex.proj {m : ℕ}
      (σ : stdSimplex ℝ (Fin (m + 1))) (h : σ 0 ≠ 1) : stdSimplex ℝ (Fin m) :=
  ⟨(1 - σ 0) ⁻¹ • σ ∘ Fin.succ,
  fun i ↦ mul_nonneg (by simp) (by simp), (by
    simpa [← Finset.mul_sum, inv_mul_eq_iff_eq_mul₀, h, sub_eq_iff_eq_add, @eq_comm ℝ 1,
      eq_sub_iff_add_eq', Fin.sum_univ_succ] using σ.prop.right)⟩

lemma stdSimplex.apply_zero_eq_one_iff {m : ℕ} (σ : stdSimplex ℝ (Fin (m + 1))) :
    σ 0 = 1 ↔ ∀ (i : Fin m), σ i.succ = 0 := by
  refine ⟨fun hσ ↦ ?_, fun hσ ↦ ?_⟩ <;>
    simpa [Fin.sum_univ_succ, ← stdSimplex.coe_def, hσ, Finset.sum_eq_zero_iff_of_nonneg,
      -stdSimplex.sum_eq_one] using stdSimplex.sum_eq_one σ

noncomputable
def stdSimplex.projStdSimplex
    {m : ℕ} (σ : StdSimplex ℝ ↑(stdSimplex ℝ (Fin (m + 1)))) (H : σ.sConvexCombo 0 ≠ 1) :
    StdSimplex ℝ ↑(stdSimplex ℝ (Fin m)) := by
  refine ⟨(1 - σ.sConvexCombo 0)⁻¹ • (σ.weights.comapDomain (α := { σ // σ 0 ≠ 1 }) _
    Subtype.val_injective.injOn).sum fun σ r ↦ .single (proj _ σ.2) ((1 - σ.1 0) * r), ?_, ?_⟩
  · refine smul_nonneg (by simp) (Finsupp.sum_nonneg fun x hx ↦ ?_)
    simp only [ne_eq, Finsupp.comapDomain_apply, Finsupp.single_nonneg]
    exact mul_nonneg (by simp) (by simpa using σ.nonneg _)
  · classical
    suffices ((σ.weights.comapDomain (α := { σ // σ 0 ≠ 1 }) _ Subtype.val_injective.injOn).sum
        fun a b ↦ (1 - a.1 0) * b) = 1 - σ.sConvexCombo 0 by
      simp [Finsupp.sum_sum_index, Finsupp.sum_smul_index, ← Finsupp.mul_sum,
        this, sub_eq_zero, H.symm]
    trans σ.weights.sum fun x r ↦ (1 - x 0) * r
    · simp +contextual [Finsupp.sum, Finset.sum_preimage' (g := fun x ↦ (1 - x 0) * σ.weights x),
        Finset.sum_subset (Finset.filter_subset _ _)]
    rw [eq_sub_iff_add_eq]
    simp [stdSimplex.coe_def, sConvexCombo_eq_sum, StdSimplex.map, Finsupp.sum_mapDomain_index,
      add_mul, Finsupp.sum_apply', ← Finsupp.sum_add, mul_comm (_ - _), ← mul_add]

lemma stdSimplex.proj_sConvexCombo {m : ℕ} (σ : StdSimplex ℝ ↑(stdSimplex ℝ (Fin (m + 1))))
    (H : σ.sConvexCombo 0 ≠ 1) :
    stdSimplex.proj (sConvexCombo σ) H = sConvexCombo (R := ℝ) (stdSimplex.projStdSimplex σ H) := by
  classical
  ext i
  suffices σ.weights.sum (fun a r ↦ r • a.1) i.succ =
      (σ.weights.comapDomain (α := { σ // σ 0 ≠ 1 }) _ Subtype.val_injective.injOn).sum
        (fun a r ↦ r • a.1.1 ∘ Fin.succ) i by
    have H (σ : { σ : stdSimplex ℝ (Fin (m + 1)) // ¬ σ.1 0 = 1 }) : 1 - σ.1.1 0 ≠ 0 := by
      simpa [sub_eq_zero] using Ne.symm σ.2
    dsimp [stdSimplex.proj, stdSimplex.projStdSimplex]
    simp [stdSimplex.coe_def, sConvexCombo_eq_sum, StdSimplex.map,
      Finsupp.sum_mapDomain_index, Finsupp.sum_sum_index, Finsupp.sum_smul_index,
      ← Finsupp.smul_sum, mul_smul, add_smul, smul_comm (_ - _), H, this]
  suffices ∑ x ∈ σ.weights.support, σ.weights x * x i.succ =
      ∑ x ∈ σ.weights.support with ¬x 0 = 1, σ.weights x * x i.succ by
    simpa [Finsupp.sum, Finset.sum_preimage' (g := fun x ↦ σ.weights x * x.1 i.succ)]
  refine (Finset.sum_subset (Finset.filter_subset _ _) fun x hx hx' ↦ ?_).symm
  simp_all [stdSimplex.apply_zero_eq_one_iff]

lemma stdSimplex.sConvexCombo_apply {ι : Type*} [Fintype ι]
    (f : StdSimplex ℝ ↑(stdSimplex ℝ ι)) (x) :
    letI : ConvexSpace ℝ ℝ := inferInstance
    ConvexSpace.sConvexCombo f x = ConvexSpace.sConvexCombo (f.map (· x)) := by
  rw [coe_def, ofConvex.coe_sConvexCombo, sConvexCombo_eq_sum]
  simp [Finsupp.sum_mapDomain_index, add_mul, Finsupp.sum_apply',
    sConvexCombo_eq_sum, coe_def, StdSimplex.map]

lemma IsAffineMap.map_convexComboPair {f : M → N} (hf : IsAffineMap R f)
    (m₁ m₂ : M) (s₁ s₂ : R) (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂) (hs₁s₂ : s₁ + s₂ = 1) :
    f (convexComboPair s₁ s₂ hs₁ hs₂ hs₁s₂ m₁ m₂) =
      convexComboPair s₁ s₂ hs₁ hs₂ hs₁s₂ (f m₁) (f m₂) := by
  simp [convexComboPair, hf.map_sConvexCombo]

noncomputable def stdSimplex.cone {m : ℕ} (p : X)
      (α : C(stdSimplex ℝ (Fin m), X)) :
    C(stdSimplex ℝ (Fin (m + 1)), X) where
  toFun σ := convexComboPair (σ 0) (1 - σ 0) (by simp) (by simp) (by simp) p
    (if h : σ 0 = 1 then p else α (proj σ h))
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

lemma stdSimplex.cone_apply_of_eq_one {m : ℕ} (p : X) (α : C(stdSimplex ℝ (Fin m), X))
      (σ : stdSimplex ℝ (Fin (m + 1))) (H : σ 0 = 1) :
    cone p α σ = p := by
  simp [H, cone]

lemma stdSimplex.cone_apply {m : ℕ} (p : X) (α : C(stdSimplex ℝ (Fin m), X))
      (σ : stdSimplex ℝ (Fin (m + 1))) (σ' : stdSimplex ℝ (Fin m))
      (H : (1 - σ 0) • σ'.1 = σ ∘ Fin.succ) :
    cone p α σ =
      convexComboPair (σ 0) (1 - σ 0) (by simp) (by simp) (by simp) p (α σ') := by
  by_cases h : σ 0 = 1
  · simp [h, convexComboPair_one, cone_apply_of_eq_one]
  · simp [cone, proj, h, ← H, show 1 - σ 0 ≠ 0 by simpa [sub_eq_zero] using Ne.symm h]

noncomputable def stdSimplex.isAffine_cone {m : ℕ} (p : X) (α : C(stdSimplex ℝ (Fin m), X))
    (H : IsAffineMap ℝ α) : IsAffineMap ℝ (cone p α) := by
  classical
  refine ⟨fun s ↦ ?_⟩
  symm
  dsimp [cone]
  by_cases hs0 : s.sConvexCombo 0 = 1
  · trans sConvexCombo (s.map fun _ ↦ p)
    · congr 1
      refine StdSimplex.ext <| Finsupp.mapDomain_congr fun x hx ↦ ?_
      suffices x 0 = 1 by simp [this, convexComboPair_same]
      rw [stdSimplex.apply_zero_eq_one_iff] at hs0 ⊢
      replace hs0 : ∀ (i : Fin m), s.weights.sum (fun a r ↦ r • a.1) i.succ = 0 := by
        simpa [stdSimplex.coe_def, sConvexCombo_eq_sum, StdSimplex.map,
          Finsupp.sum_mapDomain_index, add_smul] using hs0
      intro i
      simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs0
      have := (Finset.sum_eq_zero_iff_of_nonneg
        fun x hx ↦ mul_nonneg (s.nonneg _) (x.2.1 _)).mp (hs0 i) x hx
      simp_all [← stdSimplex.coe_def]
    · simp [hs0, convexComboPair_same]
  simp only [hs0, ↓reduceDIte, proj_sConvexCombo, H.map_sConvexCombo]
  simp_rw [← iConvexCombo.eq_def, convexComboPair_iConvexCombo_right, iConvexCombo_convexComboPair]
  congr 1
  ext1
  rw [(StdSimplex.isAffineMap_weights ..).map_iConvexCombo,
    (StdSimplex.isAffineMap_weights ..).map_convexComboPair, convexComboPair_eq_add]
  suffices s.weights.sum (fun i r ↦ r • (StdSimplex.duple p
        (if h : i 0 = 1 then p else α (proj i h)) (s := i 0) (t := 1 - i 0) sorry sorry
          sorry).weights) =
      Finsupp.single p (s.sConvexCombo 0) +
        (1 - s.sConvexCombo 0) • (projStdSimplex s hs0).weights.mapDomain α by
    simpa [Function.comp_def, ← StdSimplex.mk_single, StdSimplex.map,
      iConvexCombo_eq_sum]
  rw [← Finsupp.mapDomain_smul]
  dsimp [projStdSimplex]
  simp only [ne_eq, sub_eq_zero, Ne.symm hs0, not_false_eq_true, smul_inv_smul₀,
    Finsupp.mapDomain_sum']
  simp only [Finsupp.sum, smul_add, Finsupp.smul_single,
    smul_eq_mul, Finsupp.comapDomain_support, Finsupp.comapDomain_apply, Finsupp.mapDomain_single]
  rw [Finset.sum_add_distrib]
  nth_rw 2 [← Finset.sum_filter_add_sum_filter_not s.weights.support (p := (· 0 = 1))]
  rw [Finset.sum_congr (s₁ := .filter _ _) rfl fun x hx ↦ by rw [dif_pos (by simp_all)]]
  rw [← Finsupp.single_finset_sum, ← Finsupp.single_finset_sum, ← add_assoc, ← Finsupp.single_add]
  congr 1
  · congr 1
    rw [(Finset.filter _ _).sum_eq_zero (by simp_all)]
    simp [sConvexCombo_eq_sum, stdSimplex.coe_def, Finsupp.sum_mapDomain_index, add_smul]
    simp [Finsupp.sum]
  · rw [← Finset.sum_preimage (ι := { σ // ¬ σ 0 = 1 }) _ _ Subtype.val_injective.injOn]
    · refine Finset.sum_congr ?_ fun x hx ↦ ?_
      · ext ⟨x, hx⟩; simp_all
      · simp [x.2, mul_comm]
    · simp_all

end Convexity
