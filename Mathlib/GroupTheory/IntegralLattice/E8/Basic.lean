/-
Copyright (c) 2024 Erik van der Plas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik van der Plas
2025-02-26 10:09:13
E8 格子のために借用
-/
import Mathlib.GroupTheory.IntegralLattice.Equiv
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Algebra.Lie.CartanMatrix


universe u

open IntegralLattice
open FiniteDimensional

/--
The E8 lattice is the unique even, unimodular integral lattice of rank 8
-/
class E8Lattice (Λ : Type*) extends IntegralLattice Λ where
  (even : IsEven Λ)
  (unimodular : IsUnimodular Λ)
  (rank_eq_8 : finrank ℤ Λ = 8)


namespace E8Lattice

variable (Λ : Type*) [E8Lattice Λ]

theorem unique (Λ₁ Λ₂ : Type*) [E8Lattice Λ₁] [E8Lattice Λ₂]:
  Nonempty (Λ₁ ≃ₗ Λ₂) := sorry


def B := Matrix.toBilin' CartanMatrix.E₈

/- CartanMatrix.E₈ は以下の行列：
  Matrix.of
  ![![ 2,  0, -1,  0,  0,  0,  0,  0],
    ![ 0,  2,  0, -1,  0,  0,  0,  0],
    ![-1,  0,  2, -1,  0,  0,  0,  0],
    ![ 0, -1, -1,  2, -1,  0,  0,  0],
    ![ 0,  0,  0, -1,  2, -1,  0,  0],
    ![ 0,  0,  0,  0, -1,  2, -1,  0],
    ![ 0,  0,  0,  0,  0, -1,  2, -1],
    ![ 0,  0,  0,  0,  0,  0, -1,  2]]
-/

/- CartanMatrix.E₈ を上三角になるよう基本変形：
  Matrix.of
  ![![ 2,  0, -1,  0,  0,  0,  0,  0],
    ![ 0,  2,  0, -1,  0,  0,  0,  0],
    ![ 0,  0,3/2, -1,  0,  0,  0,  0],
    ![ 0,  0,  0,5/6, -1,  0,  0,  0],
    ![ 0,  0,  0,  0,4/5, -1,  0,  0],
    ![ 0,  0,  0,  0,  0,3/4, -1,  0],
    ![ 0,  0,  0,  0,  0,  0,2/3, -1],
    ![ 0,  0,  0,  0,  0,  0,  0,1/2]]
-/

#eval 2 * 2 * 3/2 * 5/6 * 4/5 * 3/4 * 2/3 * 1/2 -- = 1

lemma cartan_det : (CartanMatrix.E₈).det = 1 := by
  sorry


-- 自身との bilinear form を具体的に計算．
lemma inner_self_calc (x : Fin 8 → ℤ) : (B x) x =
  2 * ((x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 + (x 3) ^ 2 + (x 4) ^ 2 + (x 5) ^ 2 + (x 6) ^ 2 + (x 7) ^ 2
  - ((x 0 * x 2) + (x 1 * x 3) + (x 2 * x 3) + (x 3 * x 4) + (x 4 * x 5) + (x 5 * x 6) + (x 6 * x 7))) := by
    rw [B]
    rw [Matrix.toBilin'_apply', CartanMatrix.E₈] -- bilinear form を内積の形に展開(x ⬝ (Ay) = x^t A y)
    simp
    simp [Matrix.vecHead, Matrix.vecTail, Fin.succ] -- 内積を力技で計算
    ring_nf

-- 自身との bilinear form を平方完成
lemma inner_self_comp_sq (x : Fin 8 → ℤ) : (B x) x =
  (√2 * x 0 - √(1 / 2) * x 2) ^ 2 + (√2 * x 1 - √(1 / 2) * x 3) ^ 2 + (√(3 / 2) * x 2 - √(2 / 3) * x 3) ^ 2 +
  (√(5 / 6) * x 3 - √(6 / 5) * x 4) ^ 2 + (√(4 / 5) * x 4 - √(5 / 4) * x 5) ^ 2 +
  (√(3 / 4) * x 5 - √(4 / 3) * x 6) ^ 2 + (√(2 / 3) * x 6 - √(3 / 2) * x 7) ^ 2 + (1 / 2) * x 7 ^ 2 := by
    rw [inner_self_calc]
    ring_nf
    simp
    ring_nf
    simp [mul_inv_cancel]

instance exampleE8 : E8Lattice (Fin 8 → ℤ) where
  inner := fun x y => B x y
  add := Pi.addCommGroup.add
  add_assoc := Pi.addCommGroup.add_assoc
  zero := Pi.addCommGroup.zero
  zero_add := Pi.addCommGroup.zero_add
  add_zero := Pi.addCommGroup.add_zero
  nsmul := Pi.addCommGroup.nsmul
  nsmul_zero := Pi.addCommGroup.nsmul_zero
  nsmul_succ := Pi.addCommGroup.nsmul_succ
  neg := Pi.addCommGroup.neg
  sub := Pi.addCommGroup.sub
  sub_eq_add_neg := Pi.addCommGroup.sub_eq_add_neg
  zsmul := Pi.addCommGroup.zsmul
  zsmul_zero' := Pi.addCommGroup.zsmul_zero'
  zsmul_succ' := Pi.addCommGroup.zsmul_succ'
  zsmul_neg' := Pi.addCommGroup.zsmul_neg'
  add_left_neg := Pi.addCommGroup.add_left_neg
  add_comm := Pi.addCommGroup.add_comm
  free := by exact Module.Free.function (Fin 8) ℤ ℤ
  finite := by exact Module.Finite.pi
  add_inner := by
    intros
    rw [inner, B]
    simp
  inner_sym := by
    intros
    rw [inner, B]
    simp
    simp [Matrix.toBilin'_apply']
    rw [CartanMatrix.E₈]
    simp -- 力技で計算
    ring
  inner_self := by
    intro x
    simp [inner]
    have (a : ℤ) : (0 : ℤ) ≤ a ↔ (0 : ℝ) ≤ (a : ℝ) := by simp -- (整数) ≤ (整数) ↔ (実数) ≤ (実数) の変換
    rw [this, inner_self_comp_sq]
    repeat'
      apply add_nonneg
    repeat'
      apply sq_nonneg
    apply mul_nonneg
    · apply div_nonneg
      <;> norm_num
    · apply sq_nonneg
  inner_self_eq_zero := by
    intro x h
    simp [inner] at h
    have coe (a : ℤ) : a = (0 : ℤ) ↔ (a : ℝ) = (0 : ℝ) := by simp -- (整数) = (整数) ↔ (実数) = (実数) の変換
    rw [coe, inner_self_comp_sq] at h -- B x x を平方完成した形にする
    -- f₀ + ... + f₇ = 0 ↔ f₀ = ... = f₇ = 0
    rw [add_eq_zero_iff'] at h
    rw [add_eq_zero_iff'] at h
    rw [add_eq_zero_iff'] at h
    rw [add_eq_zero_iff'] at h
    rw [add_eq_zero_iff'] at h
    rw [add_eq_zero_iff'] at h
    rw [add_eq_zero_iff'] at h
    rcases h with ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
    have H (a b : ℤ) (s t : ℝ) : (s * a - t * b) ^ 2 = 0 → s * a = t * b := by
      intro h
      rw [sq_eq_zero_iff] at h
      rw [sub_eq_zero] at h
      assumption
    have H' (a : ℤ) (s : ℝ) (hs : s ≠ 0) : s * a ^ 2 = 0 → a = 0 := by
      intro h
      rw [mul_eq_zero] at h
      rcases h with (h | h)
      · contradiction
      · rw [sq_eq_zero_iff, ← coe] at h
        assumption
    apply H at h0
    apply H at h1
    apply H at h2
    apply H at h3
    apply H at h4
    apply H at h5
    apply H at h6
    apply H' at h7
    simp [h7] at h6
    simp [h6] at h5
    simp [h5] at h4
    simp [h4] at h3
    simp [h3] at h2
    simp [h3] at h1
    simp [h2] at h0
    ext i -- 各 i : Fin 8 について証明する
    simp -- 0 i = 0
    fin_cases i -- i = 0, ..., 7 でしらみつぶし
    repeat'
      simp
    repeat'
      assumption
    repeat'
      apply sq_nonneg
    repeat'
      apply add_nonneg
    repeat'
      apply sq_nonneg
  even := by
    rw [IsEven]
    intro x
    rw [Even]
    simp [inner]
    rw [inner_self_calc]
    use (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 + (x 3) ^ 2 + (x 4) ^ 2 + (x 5) ^ 2 + (x 6) ^ 2 + (x 7) ^ 2
      - ((x 0 * x 2) + (x 1 * x 3) + (x 2 * x 3) + (x 3 * x 4) + (x 4 * x 5) + (x 5 * x 6) + (x 6 * x 7))
    ring
  unimodular := by
    rw [IsUnimodular, determinant]
    --determinant, Matrix.det_apply']
    sorry
  rank_eq_8 := by exact finrank_fin_fun ℤ


-- Type u だとできない．
theorem exists_E8 : ∃ (Λ : Type u), Nonempty (E8Lattice Λ) := sorry

-- Type 0 ならできる．
theorem exists_E8' : ∃ (Λ : Type), Nonempty (E8Lattice Λ) := by
  use (Fin 8 → ℤ)
  exact ⟨E8Lattice.exampleE8⟩

instance (n : ℕ) : Finite {x: Λ | ⟪x, x⟫_ℤ = n} := sorry
instance (n : ℕ) : Finite {x: Λ // ⟪x, x⟫_ℤ = n} := sorry

-- Lemma's about cardinality of vectors of norms 2, 4, 6 and 8:


lemma card_norm_2 : Nat.card {x: Λ | ⟪x, x⟫_ℤ = 2} = 240 := sorry

end E8Lattice
