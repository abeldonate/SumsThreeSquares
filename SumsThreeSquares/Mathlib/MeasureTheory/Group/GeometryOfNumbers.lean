/-
Copyright (c) 2026 Abel Doñate Muñoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abel Doñate Muñoz
-/
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Group.GeometryOfNumbers

/-!
# Minkowski's convex body theorem for `ℤⁿ`

This file specialises `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`
to the standard lattice `ℤⁿ ⊆ ℝⁿ`.
-/

open Module

namespace MeasureTheory

/-- **Minkowski's convex body theorem** for the standard lattice `ℤⁿ ⊆ ℝⁿ`: a convex symmetric
set of volume greater than `2 ^ n` contains a nonzero point with integer coordinates. -/
theorem exists_ne_zero_int_mem_of_two_pow_card_lt_volume {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s)
    (h : 2 ^ Fintype.card ι < volume s) : ∃ x : ι → ℤ, x ≠ 0 ∧ ((↑) ∘ x : ι → ℝ) ∈ s := by
  have : Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ _))
  obtain ⟨⟨x, hx⟩, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ ι) volume) h_symm h_conv
    (by simpa [ZSpan.fundamentalDomain_pi_basisFun, Real.volume_pi_Ico] using h)
  choose n hn using ((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ x).1 hx
  refine ⟨n, fun h0 ↦ hx0 ?_, ?_⟩
  · ext i; simpa [h0] using (hn i).symm
  · convert hxs; ext i; simpa using hn i

end MeasureTheory
