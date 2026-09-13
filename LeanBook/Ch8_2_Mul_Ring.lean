import LeanBook.Ch8_1_Add_Abel

/-- 単位元が何であるかを指定する -/
instance : Zero MyNat where
  zero := 0

/-- MyNatは可換なモノイド -/
instance : AddCommMonoid MyNat where
  zero_add := MyNat.zero_add
  add_zero := MyNat.add_zero
  add_assoc := MyNat.add_assoc
  add_comm := MyNat.add_comm
  nsmul := nsmulRec

/-- 掛け算の単位元を指定する -/
instance : One MyNat where
  one := 1

/-- MyNat は可換な半環 -/
instance : CommSemiring MyNat where
  left_distrib := MyNat.mul_add
  right_distrib := MyNat.add_mul
  zero_mul := MyNat.zero_mul
  mul_zero := MyNat.mul_zero
  mul_one := MyNat.mul_one
  one_mul := MyNat.one_mul
  mul_assoc := MyNat.mul_assoc
  mul_comm := MyNat.mul_comm

example (a b c : MyNat) : (a + b) * (a + c) = a * a + (b + c) * a + b * c := by
  -- 分配法則や交換法則を自動で使って証明をしてくれるようになった
  ring

/-- (m₁ - m₂) * (n₁ - n₂) = (m₁ * n₁ + m₂ * n₂) - (m₁ * n₂ + m₂ * n₁) -/
def PreInt.mul (m n : PreInt) : MyInt :=
  match m, n with
  | (m₁, m₂), (n₁, n₂) => ⟦(m₁ * n₁ + m₂ * n₂, m₁ * n₂ + m₂ * n₁)⟧

/-- 整数の掛け算-/
def MyInt.mul : MyInt → MyInt → MyInt :=
  Quotient.lift₂ PreInt.mul <| by
  intro (a, b) (c, d) (p, q) (r, s) h₁ h₂
  dsimp [PreInt.mul]
  apply Quotient.sound
  simp only [sr_def] at *

  -- 左辺と右辺をそれぞれ長いので変数におく
  generalize hl : a * c + b * d + (p * s + q * r) = lhs
  generalize hr : a * d + b * c + (p * r + q * s) = rhs

-- ひたすら計算する
  have leml : lhs + q * c = c * b + b * d + d * p + p * r + r * q := calc
    _ = a * c + b * d + (p * s + q * r) + q * c := by rw [hl]
    _ = (a + q) * c + b * d + p * s + q * r := by ring
    _ = (b + p) * c + b * d + p * s + q * r := by rw [h₁]
    _ = b * c + b * d + q * r + p * (c + s) := by ring
    _ = b * c + b * d + q * r + p * (d + r) := by rw [h₂]
    _ = c * b + b * d + d * p + p * r + r * q := by ring

  have lemr : rhs + q * c = c * b + b * d + d * p + p * r + r * q :=  calc
    _ = a * d + b * c + (p * r + q * s) + q * c := by rw [hr]
    _ = a * d + b * c + p * r + q * (c + s) := by ring
    _ = a * d + b * c + p * r + q * (d + r) := by rw [h₂]
    _ = (a + q) * d + b * c + p * r + q * r := by ring
    _ = (b + p) * d + b * c + p * r + q * r := by rw [h₁]
    _ = c * b + b * d + d * p + p * r + r * q := by ring
  have lem : lhs + q * c = rhs + q * c := by rw [leml, lemr]
  simp_all

instance : Mul MyInt where
  mul := MyInt.mul

@[notation_simp]
theorem MyNat.toMyNat_one : MyNat.ofNat 1 = 1 := rfl

@[simp]
theorem MyInt.mul_one (M : MyInt) : M * 1 = M := by
  revert M
  unfold_int₁
  ring

@[simp]
theorem MyInt.one_mul (M : MyInt) : 1 * M = M := by
  revert M
  unfold_int₁
  ring

@[simp]
theorem MyInt.mul_zero (M : MyInt) : M * 0 = 0 := by
  revert M
  unfold_int₁

@[simp]
theorem MyInt.zero_mul (M : MyInt) : 0 * M = 0 := by
  revert M
  unfold_int₁
  ring

theorem MyInt.mul_comm (M N : MyInt) : M * N = N * M := by
  revert M N
  unfold_int₂
  ring

theorem MyInt.mul_assoc (M N K : MyInt) : M * N * K = M * (N * K) := by
  revert M N K
  unfold_int₃
  ring

theorem MyInt.left_distrib (M N K : MyInt) : M * (N + K) = M * N + M * K := by
  revert M N K
  unfold_int₃
  ring

theorem MyInt.right_distrib (M N K : MyInt) : (M + N) * K = M * K + N * K := by
  revert M N K
  unfold_int₃
  ring

instance : CommRing MyInt where
  left_distrib := MyInt.left_distrib
  right_distrib := MyInt.right_distrib
  zero_mul := MyInt.zero_mul
  mul_zero := MyInt.mul_zero
  mul_one := MyInt.mul_one
  one_mul := MyInt.one_mul
  mul_assoc := MyInt.mul_assoc
  mul_comm := MyInt.mul_comm
  zsmul := zsmulRec
  neg_add_cancel := MyInt.neg_add_cancel

example (M N : MyInt) : (M - N) * (M + N) = M * M - N * N := by
  ring
