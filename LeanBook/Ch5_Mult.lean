import LeanBook.Ch4_NatCommMonoid

def MyNat.mul (m n : MyNat) :=
  match n with
  | 0 => 0
  | n + 1 => MyNat.mul m n + m

instance : Mul MyNat where
  mul := MyNat.mul

#eval 2 * 3

/-- 右のオペランドにある(· + 1) の消去

式が単純になるわけではないので simp はつけない（つけても意味がない）
-/
theorem MyNat.mul_add_one (m n : MyNat) : m * (n + 1) = m * n + m := by
  rfl

/-- 左のオペランドにある(· + 1) の消去

s式が単純になるわけではないので simp はつけない（つけても意味がない）
-/
theorem MyNat.add_one_mul (m n : MyNat) : (m + 1) * n = m * n + n := by
  induction n with
  | zero => rfl
  | succ n ih => calc
    _ = (m + 1) * (n + 1) := by rfl
    _ = (m + 1) * n + (m + 1) := by rw [MyNat.mul_add_one]
    _ = m * n + n + (m + 1) := by rw [ih]
    _ = m * n + m + (n + 1) := by ac_rfl
    _ = m * (n + 1) + (n + 1) := by rw [MyNat.mul_add_one]

-- ## 0 や 1 を掛けたときの性質

/-- 右から 0 を掛けても0 -/
@[simp] theorem MyNat.mul_zero (m : MyNat) : m * 0 = 0 := by
  rfl

/-- 左から 0 を掛けても0 -/
@[simp] theorem MyNat.zero_mul (n : MyNat) : 0 * n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [mul_add_one, add_zero, ih]

/-- 右から 1 を掛けても変わらない-/
@[simp] theorem MyNat.mul_one (n : MyNat) : n * 1 = n := calc
  _ = n * (0 + 1) := by simp only [zero_add]
  _ = n * 0 + n := by rw [MyNat.mul_add_one]
  _ = n := by simp only [mul_zero, zero_add]

/-- 左から 1 を掛けても変わらない -/
@[simp] theorem MyNat.one_mul (n : MyNat) : 1 * n = n := calc
_ = (0 + 1) * n := by simp
_ = 0 * n + n := by rw [MyNat.add_one_mul]
_ = n := by simp

/-- 掛け算の交換法則 -/
theorem MyNat.mul_comm (m n : MyNat) : m * n = n * m := by
  induction n with
  | zero => simp only [mul_zero, zero_mul]
  | succ n ih =>
    rw [MyNat.add_one_mul]
    rw [MyNat.mul_add_one]
    rw [ih]

/-- 右から掛けたときの分配法則 -/
theorem MyNat.add_mul (l m n : MyNat) : (l + m) * n = l * n + m * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    repeat rw [MyNat.mul_add_one]
    rw [ih]
    ac_rfl

/-- 左から掛けたときの分配法則 -/
theorem MyNat.mul_add (l m n : MyNat) : l * (m + n) = l * m + l * n := by
  rw [MyNat.mul_comm]
  rw [MyNat.add_mul]
  rw [MyNat.mul_comm, MyNat.mul_comm l n]

/-- 掛け算の結合法則 -/
theorem MyNat.mul_assoc (l m n : MyNat) : l * m * n = l * (m * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    repeat rw [MyNat.mul_add]
    simp only [mul_one]
    rw [ih]

-- `ac_rfl` というタクティクに結合・交換法則を登録する
instance : Std.Associative (α := MyNat) (· * ·) where
  assoc := MyNat.mul_assoc

instance : Std.Commutative (α := MyNat) (· * ·) where
  comm := MyNat.mul_comm
