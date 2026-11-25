/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.GeomSum

/-!
# Geometric sums in ordered semirings

For `x ≥ 2` each power `x ^ (i + 1)` is at least twice `x ^ i`, so the geometric sum
`∑_{i < n} x ^ i` is at most `x ^ n - 1`. Over `ℕ` this is Mathlib's `Nat.geomSum_lt`.

## Main results

* `TauCeti.one_add_geom_sum_le_pow`: `1 + ∑_{i < n} x ^ i ≤ x ^ n` for `2 ≤ x` in an ordered
  semiring.
-/

public section

namespace TauCeti

open Finset

/-- `1 + ∑_{i < n} x ^ i ≤ x ^ n` for `2 ≤ x` in an ordered semiring. -/
theorem one_add_geom_sum_le_pow {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    {x : R} (hx : 2 ≤ x) (n : ℕ) : 1 + ∑ i ∈ range n, x ^ i ≤ x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc 1 + ∑ i ∈ range (n + 1), x ^ i = 1 + ∑ i ∈ range n, x ^ i + x ^ n := by
          rw [sum_range_succ, add_assoc]
      _ ≤ x ^ n * 2 := by rw [mul_two]; gcongr
      _ ≤ x ^ (n + 1) := by
          rw [pow_succ]
          exact mul_le_mul_of_nonneg_left hx (pow_nonneg (zero_le_two.trans hx) n)

end TauCeti
