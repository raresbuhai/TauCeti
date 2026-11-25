/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Algebra.Star.Module
public import Mathlib.Algebra.CharP.Invertible

/-!
# Hermitian matrices over `RCLike` fields

A diagonal matrix with real entries is Hermitian after scalar inclusion into any `RCLike`
field. This supplies Hermiticity witnesses for real diagonal perturbations. The self-adjoint part
`(X + Xᴴ) / 2` of a matrix is Hermitian (`Matrix.isHermitian_selfAdjointPart`). The diagonal of the
Gram matrix `A * Aᴴ` consists of the squared norms of the rows of `A`
(`Matrix.diag_mul_conjTranspose_self_apply`), so for a Hermitian `H` the diagonal of `H * H` does
too (`Matrix.IsHermitian.diag_mul_self_apply`).
-/

public section

namespace Matrix

/-- A real diagonal matrix is Hermitian over any `RCLike` field. -/
@[simp]
theorem isHermitian_diagonal_ofReal {n 𝕜 : Type*} [DecidableEq n] [RCLike 𝕜]
    (d : n → ℝ) : (diagonal fun i ↦ (d i : 𝕜)).IsHermitian := by
  simp [isHermitian_diagonal_iff, isSelfAdjoint_iff]

/-- The diagonal entries of the Gram matrix `A * Aᴴ` are the squared norms of the rows of `A`. -/
theorem diag_mul_conjTranspose_self_apply {m n 𝕜 : Type*} [Fintype n] [RCLike 𝕜]
    (A : Matrix m n 𝕜) (i : m) : (A * Aᴴ).diag i = ((∑ j, ‖A i j‖ ^ 2 : ℝ) : 𝕜) := by
  simp [Matrix.mul_apply, RCLike.mul_conj]

/-- For a Hermitian `H`, the diagonal entries of `H * H` are the squared norms of its rows. -/
theorem IsHermitian.diag_mul_self_apply {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜] {H : Matrix n n 𝕜}
    (hH : H.IsHermitian) (i : n) : (H * H).diag i = ((∑ j, ‖H i j‖ ^ 2 : ℝ) : 𝕜) := by
  rw [← diag_mul_conjTranspose_self_apply, hH.eq]

/-- The self-adjoint part `(X + Xᴴ) / 2` of a matrix is Hermitian. -/
theorem isHermitian_selfAdjointPart {n 𝕜 : Type*} [RCLike 𝕜] (X : Matrix n n 𝕜) :
    (selfAdjointPart ℝ X : Matrix n n 𝕜).IsHermitian :=
  (selfAdjoint.isSelfAdjoint (x := selfAdjointPart ℝ X)).isHermitian

end Matrix
