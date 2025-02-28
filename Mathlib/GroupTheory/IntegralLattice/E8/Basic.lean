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
  add_inner := sorry
  inner_sym := sorry
  inner_self := sorry
  inner_self_eq_zero := sorry
  even := sorry
  unimodular := sorry
  rank_eq_8 := by exact finrank_fin_fun ℤ



theorem exists_E8 : ∃ (Λ : Type u), Nonempty (E8Lattice Λ) := sorry

instance (n : ℕ) : Finite {x: Λ | ⟪x, x⟫_ℤ = n} := sorry
instance (n : ℕ) : Finite {x: Λ // ⟪x, x⟫_ℤ = n} := sorry

-- Lemma's about cardinality of vectors of norms 2, 4, 6 and 8:


lemma card_norm_2 : Nat.card {x: Λ | ⟪x, x⟫_ℤ = 2} = 240 := sorry

end E8Lattice
