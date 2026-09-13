import LeanBook.Ch8_3_Coe

-- 「m にある自然数 k を足し算すると n になる」として m ≤ n を定義する

/-- 整数の広義順序 -/
def MyInt.le (M N : MyInt) : Prop :=
  ∃ k : MyNat, M + ↑ k = N

instance : LE MyInt where
  le := MyInt.le

@[notation_simp]
theorem MyInt.le_def (M N : MyInt) :
    M ≤ N ↔ ∃ k : MyNat, M + ↑ k = N := by
  rfl

/-- 整数の狭義順序 -/
def MyInt.lt (m n : MyInt) : Prop :=
  m ≤ n ∧ ¬ n ≤ m

instance : LT MyInt where
  lt := MyInt.lt

@[notation_simp]
theorem MyInt.lt_def (a b : MyInt) :
    a < b ↔ a ≤ b ∧ ¬ (b ≤ a) := by
  rfl
