module

public import Mathlib.LinearAlgebra.ConvexSpace

public section

namespace ConvexSpace

variable {R M N P : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
    [ConvexSpace R M] [ConvexSpace R N] [ConvexSpace R P]

variable (R) in
@[fun_prop]
structure IsAffine (f : M → N) : Prop where
  convexCombination_map (s : StdSimplex R M) : convexCombination (s.map f) = f (convexCombination s)

@[fun_prop]
lemma IsAffine.id : IsAffine R (id : M → M) where
  convexCombination_map s := by simp

@[fun_prop]
lemma IsAffine.comp {g : N → P} (hg : IsAffine R g) {f : M → N} (hf : IsAffine R f) :
    IsAffine R (g ∘ f) where
  convexCombination_map s := by
    simp [StdSimplex.map_comp, hf.convexCombination_map, hg.convexCombination_map]

end ConvexSpace
