import Mathlib
import LeanBook.Ch7_2_Int

/-- 正部分も負部分も足し合わせる -/
def PreInt.add (m n : PreInt) : MyInt :=
  match m, n with
  | (m₁, m₂), (n₁, n₂) => ⟦(m₁ + n₁, m₂ + n₂)⟧

/-- liftにより引数がPreIntからそれの商をとったMyIntへと格上げされている -/
def MyInt.add : MyInt → MyInt → MyInt :=
  -- [Quotient.liftは第二引数で、異なる代表元aを選んでも関数結果が同じになることの証明を要求する]
  Quotient.lift₂ PreInt.add <| by
    intro (m₁, m₂) (n₁, n₂) (m'₁, m'₂) (n'₁, n'₂) rm rn
    dsimp [PreInt.add]
    apply Quotient.sound
    simp only [sr_def] at *
    have : m₁ + n₁ + (m'₂ + n'₂) = m₂ + n₂ + (m'₁ + n'₁) := calc
      _ = (m₁ + m'₂) + (n₁ + n'₂) := by ac_rfl
      _ = (m₂ + m'₁) + (n₂ + n'₁) := by rw [rm, rn]
      _ = m₂ + n₂ + (m'₁ + n'₁) := by ac_rfl
    assumption

instance instAddMyInt : Add MyInt where
  add := MyInt.add

#check (3 + 4 : MyInt)

@[simp]
theorem MyInt.add_def (x₁ x₂ y₁ y₂ : MyNat):
    ⟦(x₁, y₁)⟧ + ⟦(x₂, y₂)⟧ = (⟦(x₁ + x₂, y₁ + y₂)⟧ : MyInt) := by
  dsimp [(· + ·), Add.add, MyInt.add, PreInt.add,
    Quotient.lift₂, Quotient.lift, Quotient.mk]

-- notation_simp で簡単に展開できるようにする
attribute [notation_simp] PreInt.sr PreInt.r

-- notation_simp に使用させるための補題
@[notation_simp, simp] theorem MyNat.ofNat_zero : MyNat.ofNat 0 = 0 := rfl

@[simp]
theorem MyInt.add_zero (M : MyInt) : M + 0 = M := by
  -- [inductionOnは第二引数で、任意の代表元aをとっても**それの同値類Aについて**命題が成り立つことの証明を要求する]
  refine Quotient.inductionOn M ?_ -- ∀ (m : PreInt), ⟦m⟧ + 0 = ⟦m⟧
  intro (m₁, m₂)
  apply Quotient.sound -- [同値類での＝をもとの元での～に戻す]
  notation_simp
  ac_rfl

@[simp]
theorem MyInt.zero_add (M : MyInt) : 0 + M = M := by
  refine Quotient.inductionOn M ?_
  intro (m₁, m₂)
  apply Quotient.sound
  notation_simp
  ac_rfl

/-- 整数に関する命題を自然数の話に帰着させる（1 変数用） -/
macro "unfold_int₁" : tactic => `(tactic| focus
  intro m
  refine Quotient.inductionOn m ?_
  intro (a₁, a₂)
  apply Quot.sound
  notation_simp
)

example (m : MyInt) : m + 0 = m := by
  revert m -- revert でゴールを∀ m, m + 0 = m にする
  unfold_int₁
  ac_rfl

example (m : MyInt) : 0 + m = m := by
  revert m -- revert でゴールを∀ m, 0 + m = m にする
  unfold_int₁
  ac_rfl

/-- 整数に関する命題を自然数の話に帰着させる（2 変数用） -/
macro "unfold_int₂" : tactic => `(tactic| focus
  intro m n
  refine Quotient.inductionOn₂ m n ?_
  intro (a₁, a₂) (b₁, b₂)
  apply Quot.sound
  notation_simp
)

/-- 整数に関する命題を自然数の話に帰着させる（3 変数用） -/
macro "unfold_int₃" : tactic => `(tactic| focus
  intro m n k
  refine Quotient.inductionOn₃ m n k ?_
  intro (a₁, a₂) (b₁, b₂) (c₁, c₂)
  apply Quot.sound
  notation_simp
)

theorem MyInt.add_assoc (m n k : MyInt) :
    m + n + k = m + (n + k) := by
  revert m n k
  unfold_int₃
  ac_rfl

theorem MyInt.add_comm (m n : MyInt) : m + n = n + m := by
  revert m n
  unfold_int₂
  ac_rfl

-- MyInt の足し算が結合法則を満たすことを登録する
instance : Std.Associative (α := MyInt) (· + ·) where
  assoc := MyInt.add_assoc

-- MyInt の足し算が交換法則を満たすことを登録する
instance : Std.Commutative (α := MyInt) (· + ·) where
  comm := MyInt.add_comm

/-- 整数の引き算-/
def MyInt.sub (m n : MyInt) : MyInt := m + -n

/-- 引き算をa - b と書けるように型クラスに登録する -/
instance : Sub MyInt where
  sub := MyInt.sub

-- 後で使うので補題として登録しておく
@[simp, notation_simp]
theorem MyInt.sub_def (x y : MyInt) : x - y = x + -y := rfl

theorem MyInt.neg_add_cancel (m : MyInt) : -m + m = 0 := by
  revert m
  unfold_int₁
  ac_rfl

/-- 整数は足し算に関して可換な群 -/
instance : AddCommGroup MyInt where
  add_assoc := MyInt.add_assoc
  add_comm := MyInt.add_comm
  zero_add := MyInt.zero_add
  add_zero := MyInt.add_zero
  neg_add_cancel := MyInt.neg_add_cancel
  nsmul := nsmulRec
  zsmul := zsmulRec

-- abel タクティクは引き算を扱える
example (a b : MyInt) : (a + b) - b = a := by
  abel

example (a b c : MyInt) : (a - b) - c + b + c = a := by
  abel
