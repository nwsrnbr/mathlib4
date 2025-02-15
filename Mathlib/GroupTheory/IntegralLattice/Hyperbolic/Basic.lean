import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant

-- 基底は b1 := (1 / √2) [1, 1] と b2 := (1 / √2) [1, -1].
-- Hyperbolic は a * b1 + b * b2 と書いたときの a と b の組たちの集合．
@[ext]
structure Hyperbolic where
  a : ℤ
  b : ℤ

namespace Hyperbolic

def b1 : Hyperbolic :=
  ⟨1, 0⟩

def b2 : Hyperbolic :=
  ⟨0, 1⟩

instance : Zero Hyperbolic :=
  ⟨0, 0⟩

instance : Add Hyperbolic :=
  ⟨fun x y ↦ ⟨x.a + y.a, x.b + y.b⟩⟩

instance : Neg Hyperbolic :=
  ⟨fun x ↦ ⟨-x.a, -x.b⟩⟩

theorem zero_def : (0 : Hyperbolic) = ⟨0, 0⟩ :=
  rfl

theorem add_def (x y : Hyperbolic) : x + y = ⟨x.a + y.a, x.b + y.b⟩ :=
  rfl

theorem neg_def (x : Hyperbolic) : -x = ⟨-x.a, -x.b⟩ :=
  rfl

@[simp]
theorem zero_a : (0 : Hyperbolic).a = 0 :=
  rfl

@[simp]
theorem zero_b : (0 : Hyperbolic).b = 0 :=
  rfl

@[simp]
theorem add_a (x y : Hyperbolic) : (x + y).a = x.a + y.a :=
  rfl

@[simp]
theorem add_b (x y : Hyperbolic) : (x + y).b = x.b + y.b :=
  rfl

@[simp]
theorem neg_a (x : Hyperbolic) : (-x).a = -x.a :=
  rfl

@[simp]
theorem neg_b (x : Hyperbolic) : (-x).b = -x.b :=
  rfl

instance is_AddCommGroup : AddCommGroup Hyperbolic where
  zero := 0
  add := (· + ·)
  neg x := -x
  add_assoc := by
    intros
    ext <;> simp <;> ring
  zero_add := by
    intros
    ext <;> simp
  add_zero := by
    intros
    ext <;> simp
  add_left_neg := by
    intros
    ext <;> simp
  add_comm := by
    intros
    ext <;> simp <;> ring
  nsmul := fun n x => ⟨n * x.a, n * x.b⟩
  zsmul := fun n x => ⟨n * x.a, n * x.b⟩
  nsmul_zero := by
    intros
    ext <;> simp
  nsmul_succ := by
    intros
    ext <;> simp <;> ring
  zsmul_zero' := by
    intros
    ext <;> simp
  zsmul_succ' := by
    intros
    ext <;> simp <;> ring
  zsmul_neg' := by
    intros
    ext <;> simp [Int.negSucc_coe] <;> ring

-- 内積は (第1成分同士の積) - (第2成分同士の積).
-- 基底は共に (1 / √2) が係数にあるので，最後に / 2 されることに注意．
noncomputable def inner (x y : Hyperbolic) : ℝ :=
  ((x.a + x.b) * (y.a + y.b) - (x.a - x.b) * (y.a - y.b)) / 2

noncomputable def norm (x : Hyperbolic) : ℝ := inner x x

theorem inner_comm (x y : Hyperbolic) : inner x y = inner y x := by
  simp [inner]
  ring

noncomputable def Gram_matrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![inner b1 b1, inner b1 b2;
     inner b2 b1, inner b2 b2]

theorem is_even : ∀ x : Hyperbolic, ∃ n : ℤ, norm x = 2 * n := by
  intro x
  rw [norm, inner]
  ring_nf
  use x.a * x.b
  simp

theorem is_unimodular : (Gram_matrix).det = 1 ∨ (Gram_matrix).det = -1 := by
  right
  simp [Gram_matrix, inner, b1, b2]

end Hyperbolic
