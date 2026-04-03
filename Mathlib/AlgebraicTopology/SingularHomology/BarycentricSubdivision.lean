module

public import Mathlib.AlgebraicTopology.SingularHomology.AffineMap
public import Mathlib.Analysis.Convex.MetricSpace
public import Mathlib.Analysis.Convex.StdSimplex

@[expose] public section

section

open ConvexSpace

variable {R E I J M N : Type*} [PartialOrder R] [CommRing R]
    [IsStrictOrderedRing R] [ConvexSpace R M] [ConvexSpace R N] [AddCommGroup E] [Module R E]

abbrev StdSimplex.sConvexCombo (I : StdSimplex R M) : M := ConvexSpace.convexCombination I

-- instance : ConvexSpace R E := AddTorsor.instConvexSpace

-- attribute [positivity] StdSimplex.nonneg

lemma convexComboPair_eq_add (s t : R) (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (p q : E) :
    convexComboPair s t hs ht h p q = s • p + t • q := by
  classical
  simp [convexComboPair, convexCombination_eq_sum, StdSimplex.duple,
    Finsupp.sum_add_index, add_smul]

lemma StdSimplex.join_assoc (f : StdSimplex R (StdSimplex R (StdSimplex R I))) :
    f.join.join = (f.map (·.join)).join := by
  ext1
  simp [map, join, Finsupp.mapDomain, add_smul, Finsupp.sum_sum_index, Finsupp.sum_smul_index,
    Finsupp.smul_sum, mul_smul]

lemma StdSimplex.map_join (f : StdSimplex R (StdSimplex R I)) (g : I → J) :
    f.join.map g = (f.map (·.map g)).join := by
  ext1
  simp [map, join, Finsupp.mapDomain, add_smul, Finsupp.sum_sum_index, Finsupp.sum_smul_index,
    Finsupp.smul_sum]

@[simp]
lemma StdSimplex.join_single (x : StdSimplex R I) :
    join (.single x) = x := by
  ext; simp [join, ← mk_single]

lemma StdSimplex.weights_join_eq_convexCombination (f : StdSimplex R (StdSimplex R I)) :
    f.join.weights = (f.map StdSimplex.weights).sConvexCombo := by
  simp [convexCombination_eq_sum, StdSimplex.map, Finsupp.sum_mapDomain_index, add_smul, join]

noncomputable
instance : ConvexSpace R (StdSimplex R I) where
  convexCombination σ := σ.join
  assoc f := (StdSimplex.join_assoc f).symm
  single x := by simp

lemma StdSimplex.sConvexCombo_eq_join (f : StdSimplex R (StdSimplex R I)) :
    f.sConvexCombo = f.join := rfl

@[simp]
lemma StdSimplex.sConvexCombo_single (x : M) :
    (single (R := R) x).sConvexCombo = x :=
  ConvexSpace.single x

lemma StdSimplex.sConvexCombo_assoc (f : StdSimplex R (StdSimplex R M)) :
    f.sConvexCombo.sConvexCombo = (f.map sConvexCombo).sConvexCombo :=
  (ConvexSpace.assoc f).symm

lemma StdSimplex.isAffine_map {X Y : Type*} (f : X → Y) :
    ConvexSpace.IsAffine R (StdSimplex.map (R := R) f) :=
  ⟨fun s ↦ (StdSimplex.map_join s f).symm⟩

lemma ConvexSpace.IsAffine.map_sConvexCombo {f : M → N} (hf : IsAffine R f) (s : StdSimplex R M) :
    f s.sConvexCombo = (s.map f).sConvexCombo := (hf.1 s).symm

lemma StdSimplex.isAffine_weights : IsAffine R (weights (R := R) (M := I)) :=
  ⟨fun s ↦ (StdSimplex.weights_join_eq_convexCombination s).symm⟩

lemma ConvexSpace.IsAffine.map_convexComboPair {f : M → N} (hf : IsAffine R f)
    (m₁ m₂ : M) (s₁ s₂ : R) (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂) (hs₁s₂ : s₁ + s₂ = 1) :
    f (convexComboPair s₁ s₂ hs₁ hs₂ hs₁s₂ m₁ m₂) =
      convexComboPair s₁ s₂ hs₁ hs₂ hs₁s₂ (f m₁) (f m₂) := by
  simp [convexComboPair, ← hf.1]


noncomputable
def StdSimplex.iConvexCombo (s : StdSimplex R I) (f : I → M) : M := (s.map f).sConvexCombo

lemma ConvexSpace.IsAffine.map_iConvexCombo {f : M → N} (hf : IsAffine R f) (s : StdSimplex R I)
    (g : I → M) : f (s.iConvexCombo g) = s.iConvexCombo (f ∘ g) := by
  simp [StdSimplex.iConvexCombo, hf.map_sConvexCombo, StdSimplex.map_comp]

@[simp]
lemma StdSimplex.iConvexCombo_const (s : StdSimplex R I) (m : M) :
    (s.iConvexCombo fun _ ↦ m) = m := by
  simp [iConvexCombo]

@[simp]
lemma StdSimplex.iConvexCombo_single (i : I) (m : M) :
    ((single (R := R) i).iConvexCombo fun _ ↦ m) = m := by
  simp [iConvexCombo]

@[simp]
lemma StdSimplex.iConvexCombo_id (s : StdSimplex R M) :
    s.iConvexCombo id = s.sConvexCombo := by
  simp [iConvexCombo]

@[simp]
lemma StdSimplex.iConvexCombo_id' (s : StdSimplex R M) :
    (s.iConvexCombo fun x ↦ x) = s.sConvexCombo := StdSimplex.iConvexCombo_id s

lemma StdSimplex.iConvexCombo_assoc
    {J : I → Type*} (s : StdSimplex R I) (f : Π i, StdSimplex R (J i)) (g : Π i, J i → M) :
    s.iConvexCombo (fun i ↦ (f i).iConvexCombo (g i)) =
      (s.iConvexCombo fun i ↦ (f i).map (⟨i, ·⟩)).iConvexCombo (Sigma.uncurry g) := by
  simp only [StdSimplex.iConvexCombo]
  rw [← StdSimplex.map_map, ← StdSimplex.sConvexCombo_assoc]
  congr 1
  simp only [StdSimplex.sConvexCombo_eq_join , StdSimplex.map_join, StdSimplex.map_map]
  rfl

lemma StdSimplex.iConvexCombo_map (s : StdSimplex R I) (f : I → J) (g : J → M) :
  (s.map f).iConvexCombo g = s.iConvexCombo (g ∘ f) := by
  simp only [StdSimplex.iConvexCombo, map_comp]

lemma StdSimplex.iConvexCombo_congr (s : StdSimplex R I) (f : I ≃ J) (g : I → M) :
  s.iConvexCombo g = (s.map f).iConvexCombo (g ∘ f.symm) := by
  simp [StdSimplex.iConvexCombo_map, Function.comp_def]

lemma StdSimplex.iConvexCombo_eq_sum (f : StdSimplex R I) (g : I → E) :
    f.iConvexCombo g = f.sum fun i r ↦ r • g i := by
  simp [iConvexCombo, sConvexCombo, convexCombination_eq_sum, map,
    Finsupp.sum_mapDomain_index, add_smul]

lemma convexComboPair_def (s t : R) (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (p q : M) :
    convexComboPair s t hs ht h p q = (StdSimplex.duple 0 1 hs ht h).iConvexCombo ![p, q] := by
  simp [StdSimplex.iConvexCombo, convexComboPair]

lemma StdSimplex.iConvexCombo_comm (f : StdSimplex R I) (g : StdSimplex R J)
    (e : I → J → M) :
    f.iConvexCombo (fun x ↦ g.iConvexCombo (e x)) =
      g.iConvexCombo (fun x ↦ f.iConvexCombo (fun y ↦ e y x)) := by
  rw [StdSimplex.iConvexCombo_assoc, StdSimplex.iConvexCombo_assoc,
    StdSimplex.iConvexCombo_congr _ (((Equiv.sigmaEquivProd I J).trans
      (Equiv.prodComm _ _)).trans (Equiv.sigmaEquivProd _ _).symm)]
  congr
  suffices (f.map (fun x ↦ g.map (fun x_1 ↦ Sigma.mk x_1 x))).join =
      (g.map (f.map ∘ Sigma.mk)).join by
    simpa [StdSimplex.iConvexCombo, (StdSimplex.isAffine_map _).map_sConvexCombo,
      StdSimplex.map_map, Function.comp_def]
  ext1
  simp [StdSimplex.join, StdSimplex.map, Finsupp.mapDomain, Finsupp.sum_sum_index, add_smul,
    Finsupp.smul_sum, mul_comm, Finsupp.sum_comm f.weights g.weights]

lemma StdSimplex.convexComboPair_iConvexCombo_iConvexCombo.{u₁, u₂}
    {J₁ : Type u₁} {J₂ : Type u₂}
    (s₁ s₂ : R) (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂) (hs₁s₂ : s₁ + s₂ = 1)
    (g₁ : StdSimplex R J₁) (g₂ : StdSimplex R J₂)
    (m₁ : J₁ → M) (m₂ : J₂ → M) :
    convexComboPair s₁ s₂ hs₁ hs₂ hs₁s₂ (g₁.iConvexCombo m₁) (g₂.iConvexCombo m₂) =
      (convexComboPair s₁ s₂ hs₁ hs₂ hs₁s₂ (g₁.map m₁) (g₂.map m₂)).sConvexCombo := by
  have := iConvexCombo_assoc (I := Fin 2) (.duple 0 1 hs₁ hs₂ hs₁s₂)
    (J := ![ULift.{max u₁ u₂} J₁, ULift.{max u₁ u₂} J₂])
    (M := M) (Fin.cons (g₁.map ULift.up) (Fin.cons (g₂.map ULift.up) nofun))
    (Fin.cons (m₁ ∘ ULift.down) (Fin.cons (m₂ ∘ ULift.down) nofun))
  simp [iConvexCombo, (StdSimplex.isAffine_map _).map_sConvexCombo, map_map, Sigma.uncurry] at this
  simpa [convexComboPair, ← convexComboPair_def]

lemma StdSimplex.iConvexCombo_convexComboPair
    (s₁ s₂ : I → R) (hs₁ : ∀ i, 0 ≤ s₁ i) (hs₂ : ∀ i, 0 ≤ s₂ i) (hs₁s₂ : ∀ i, s₁ i + s₂ i = 1)
    (f : StdSimplex R I) (m₁ m₂ : I → M) :
    f.iConvexCombo (fun i ↦ convexComboPair (s₁ i) (s₂ i) (hs₁ i) (hs₂ i) (hs₁s₂ i) (m₁ i) (m₂ i)) =
    (f.iConvexCombo fun i ↦ duple (m₁ i) (m₂ i) (hs₁ i) (hs₂ i) (hs₁s₂ i)).sConvexCombo := by
  have := iConvexCombo_assoc (I := I) (J := fun _ ↦ Fin 2) (R := R) (M := M) f
    (fun i ↦ .duple 0 1 (hs₁ i) (hs₂ i) (hs₁s₂ i)) (fun i ↦ ![m₁ i, m₂ i])
  simp [iConvexCombo, (StdSimplex.isAffine_map _).map_sConvexCombo, map_map, Sigma.uncurry] at this
  simp only [← convexComboPair.eq_def] at this
  simp only [← iConvexCombo.eq_def] at this
  simpa [convexComboPair, ← convexComboPair_def]

lemma StdSimplex.convexComboPair_iConvexCombo_right
    (s₁ s₂ : R) (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂) (hs₁s₂ : s₁ + s₂ = 1)
    (g : StdSimplex R J)
    (e : J → M) (m : M) :
    convexComboPair s₁ s₂ hs₁ hs₂ hs₁s₂ m (g.iConvexCombo e) =
      (convexComboPair s₁ s₂ hs₁ hs₂ hs₁s₂ (single m) (g.map e)).sConvexCombo := by
  simpa using convexComboPair_iConvexCombo_iConvexCombo s₁ s₂ hs₁ hs₂ hs₁s₂ g g (fun _ ↦ m) e

lemma iConvexCombo_convexComboPair (f : StdSimplex R I)
    (e₁ e₂ : I → M) (s₁ s₂ : R) (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂) (hs₁s₂ : s₁ + s₂ = 1) :
    f.iConvexCombo (fun x ↦ convexComboPair s₁ s₂ hs₁ hs₂ hs₁s₂ (e₁ x) (e₂ x)) =
    convexComboPair s₁ s₂ hs₁ hs₂ hs₁s₂ (f.iConvexCombo e₁) (f.iConvexCombo e₂) := by
  simp only [convexComboPair_def]
  convert (StdSimplex.iConvexCombo_comm (.duple 0 1 hs₁ hs₂ hs₁s₂) f ![e₁, e₂]).symm with i j j
  · fin_cases j <;> simp
  · fin_cases j <;> simp

lemma convexCombination_convexComboPair_comm_right (f : StdSimplex R I)
    (m : M) (e : I → M) (s₁ s₂ : R) (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂) (hs₁s₂ : s₁ + s₂ = 1) :
    f.iConvexCombo (convexComboPair s₁ s₂ hs₁ hs₂ hs₁s₂ m <| e ·) =
    convexComboPair s₁ s₂ hs₁ hs₂ hs₁s₂ m (f.iConvexCombo e) := by
  simpa using iConvexCombo_convexComboPair f (fun _ ↦ m) e s₁ s₂ hs₁ hs₂ hs₁s₂

lemma isAffine_convexComboPair
    (m : M) (s₁ s₂ : R) (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂) (hs₁s₂ : s₁ + s₂ = 1) :
    IsAffine R (convexComboPair s₁ s₂ hs₁ hs₂ hs₁s₂ m) :=
  ⟨fun f ↦ by simpa using convexCombination_convexComboPair_comm_right f m id s₁ s₂ hs₁ hs₂ hs₁s₂⟩

end

variable {X : Type*} [ConvexSpace ℝ X] [MetricSpace X] [IsConvexMetricSpace X] [BoundedSpace X]

noncomputable
instance (n) [Fintype n] : ConvexSpace ℝ ↑(stdSimplex ℝ n) := .ofConvex (convex_stdSimplex ..)

instance (n) [Fintype n] : IsConvexMetricSpace ↑(stdSimplex ℝ n) :=
  .of_convex (convex_stdSimplex ..)

instance (n) [Fintype n] : CompactSpace ↑(stdSimplex ℝ n) :=
  isCompact_iff_compactSpace.mp (isCompact_stdSimplex _ _)

instance {T : Type*} [PseudoMetricSpace T] [CompactSpace T] : BoundedSpace T :=
  ⟨(isCompact_iff_totallyBounded_isComplete.mp isCompact_univ).1.isBounded⟩

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
    simp [stdSimplex.coe_def, convexCombination_eq_sum, StdSimplex.map,
      Finsupp.sum_mapDomain_index, add_mul, Finsupp.sum_apply', ← Finsupp.sum_add,
      mul_comm (_ - _), ← mul_add]

lemma stdSimplex.proj_convexCombination {m : ℕ} (σ : StdSimplex ℝ ↑(stdSimplex ℝ (Fin (m + 1))))
    (H : σ.sConvexCombo 0 ≠ 1) :
    stdSimplex.proj (convexCombination σ) H = convexCombination (R := ℝ)
      (stdSimplex.projStdSimplex σ H) := by
  classical
  ext i
  suffices σ.weights.sum (fun a r ↦ r • a.1) i.succ =
      (σ.weights.comapDomain (α := { σ // σ 0 ≠ 1 }) _ Subtype.val_injective.injOn).sum
        (fun a r ↦ r • a.1.1 ∘ Fin.succ) i by
    have H (σ : { σ : stdSimplex ℝ (Fin (m + 1)) // ¬ σ.1 0 = 1 }) : 1 - σ.1.1 0 ≠ 0 := by
      simpa [sub_eq_zero] using Ne.symm σ.2
    dsimp [stdSimplex.proj, stdSimplex.projStdSimplex]
    simp [stdSimplex.coe_def, convexCombination_eq_sum, StdSimplex.map,
      Finsupp.sum_mapDomain_index, Finsupp.sum_sum_index, Finsupp.sum_smul_index,
      ← Finsupp.smul_sum, mul_smul, add_smul, smul_comm (_ - _), H, this]
  suffices ∑ x ∈ σ.support, σ.weights x * x i.succ =
      ∑ x ∈ σ.support with ¬x 0 = 1, σ.weights x * x i.succ by
    simpa [Finsupp.sum, Finset.sum_preimage' (g := fun x ↦ σ.weights x * x.1 i.succ)]
  refine (Finset.sum_subset (Finset.filter_subset _ _) fun x hx hx' ↦ ?_).symm
  simp_all [stdSimplex.apply_zero_eq_one_iff]

lemma stdSimplex.convexCombination_apply {ι : Type*} [Fintype ι]
    (f : StdSimplex ℝ ↑(stdSimplex ℝ ι)) (x) :
    letI : ConvexSpace ℝ ℝ := inferInstance
    ConvexSpace.convexCombination f x = ConvexSpace.convexCombination (f.map (· x)) := by
  rw [coe_def, ofConvex.coe_convexCombination, convexCombination_eq_sum]
  simp [Finsupp.sum_mapDomain_index, add_mul, Finsupp.sum_apply',
    convexCombination_eq_sum, coe_def, StdSimplex.map]

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

lemma Finsupp.mapDomain_sum' {α β γ M N : Type*}
    [AddCommMonoid M] [Zero N] {f : α → β} {s : γ →₀ N} {v : γ → N → α →₀ M} :
    mapDomain f (s.sum v) = s.sum fun a b ↦ mapDomain f (v a b) :=
  map_finsuppSum (mapDomain.addMonoidHom f : (α →₀ M) →+ β →₀ M) _ _

noncomputable def stdSimplex.isAffine_cone {m : ℕ} (p : X)
      (α : C(stdSimplex ℝ (Fin m), X)) (H : ConvexSpace.IsAffine ℝ α) :
    ConvexSpace.IsAffine ℝ (cone p α) := by
  classical
  refine ⟨fun s ↦ ?_⟩
  dsimp [cone]
  by_cases hs0 : s.sConvexCombo 0 = 1
  · trans convexCombination (s.map fun _ ↦ p)
    · congr 1
      refine StdSimplex.ext <| Finsupp.mapDomain_congr fun x hx ↦ ?_
      suffices x 0 = 1 by simp [this, convexComboPair_same]
      rw [stdSimplex.apply_zero_eq_one_iff] at hs0 ⊢
      replace hs0 : ∀ (i : Fin m), s.sum (fun a r ↦ r • a.1) i.succ = 0 := by
        simpa [stdSimplex.coe_def, convexCombination_eq_sum, StdSimplex.map,
          Finsupp.sum_mapDomain_index, add_smul] using hs0
      intro i
      simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs0
      have := (Finset.sum_eq_zero_iff_of_nonneg
        fun x hx ↦ mul_nonneg (s.nonneg _) (x.2.1 _)).mp (hs0 i) x hx
      simp_all [← stdSimplex.coe_def]
    · simp [hs0, convexComboPair_same]
  simp only [hs0, ↓reduceDIte, proj_convexCombination, ← H.1]
  simp_rw [← StdSimplex.sConvexCombo.eq_def, ← StdSimplex.iConvexCombo.eq_def,
    StdSimplex.convexComboPair_iConvexCombo_right, StdSimplex.iConvexCombo_convexComboPair]
  congr 1
  ext1
  rw [StdSimplex.isAffine_weights.map_iConvexCombo,
    StdSimplex.isAffine_weights.map_convexComboPair, convexComboPair_eq_add]
  suffices s.sum (fun i r ↦ r • (StdSimplex.duple p
        (if h : i 0 = 1 then p else α (proj i h)) (s := i 0) (t := 1 - i 0) _ _ _).weights) =
      Finsupp.single p (s.sConvexCombo 0) +
        (1 - s.sConvexCombo 0) • (projStdSimplex s hs0).weights.mapDomain α by
    simpa [Function.comp_def, ← StdSimplex.mk_single, StdSimplex.map,
      StdSimplex.iConvexCombo_eq_sum]
  rw [← Finsupp.mapDomain_smul]
  dsimp [projStdSimplex]
  simp only [ne_eq, sub_eq_zero, Ne.symm hs0, not_false_eq_true, smul_inv_smul₀,
    Finsupp.mapDomain_sum']
  simp only [Finsupp.sum, StdSimplex.duple, smul_add, Finsupp.smul_single,
    smul_eq_mul, Finsupp.comapDomain_support, Finsupp.comapDomain_apply, Finsupp.mapDomain_single]
  rw [Finset.sum_add_distrib]
  nth_rw 2 [← Finset.sum_filter_add_sum_filter_not s.support (p := (· 0 = 1))]
  rw [Finset.sum_congr (s₁ := .filter _ _) rfl fun x hx ↦ by rw [dif_pos (by simp_all)]]
  rw [← Finsupp.single_finset_sum, ← Finsupp.single_finset_sum, ← add_assoc, ← Finsupp.single_add]
  congr 1
  · congr 1
    rw [(Finset.filter _ _).sum_eq_zero (by simp_all)]
    simp [StdSimplex.sConvexCombo, convexCombination_eq_sum, stdSimplex.coe_def,
      StdSimplex.map, Finsupp.sum_mapDomain_index, add_smul]
    simp [Finsupp.sum]
  · rw [← Finset.sum_preimage (ι := { σ // ¬ σ 0 = 1 }) _ _ Subtype.val_injective.injOn]
    · refine Finset.sum_congr ?_ fun x hx ↦ ?_
      · ext ⟨x, hx⟩; simp_all
      · simp [x.2, mul_comm]
    · simp_all

lemma stdSimplex.isAffine_map {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y) :
    IsAffine ℝ (map (S := ℝ) f) := by
  refine ⟨fun s ↦ ?_⟩
  sorry
