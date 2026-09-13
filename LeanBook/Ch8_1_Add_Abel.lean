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
  refine Quotient.inductionOn M ?_ -- [商の要素を任意の代表元からみた同値類へと書き直す]
  intro (m₁, m₂)
  apply Quotient.sound -- [同値類をもとの元に戻す]
  notation_simp
  ac_rfl

/-- 整数に関する命題を自然数の話に帰着させる（1 変数用） -/
macro "unfold_int₁" : tactic => `(tactic| focus
  intro M
  refine Quotient.inductionOn M ?_
  intro (a₁, a₂)
  apply Quot.sound
  notation_simp
)

example (M : MyInt) : M + 0 = M := by
  revert M -- revert でゴールを∀ M, M + 0 = M にする
  unfold_int₁
  ac_rfl

example (M : MyInt) : 0 + M = M := by
  revert M -- revert でゴールを∀ M, 0 + M = M にする
  unfold_int₁
  ac_rfl

/-- 整数に関する命題を自然数の話に帰着させる（2 変数用） -/
macro "unfold_int₂" : tactic => `(tactic| focus
  intro M N
  refine Quotient.inductionOn₂ M N ?_
  intro (a₁, a₂) (b₁, b₂)
  apply Quot.sound
  notation_simp
)

/-- 整数に関する命題を自然数の話に帰着させる（3 変数用） -/
macro "unfold_int₃" : tactic => `(tactic| focus
  intro M N K
  refine Quotient.inductionOn₃ M N K ?_
  intro (a₁, a₂) (b₁, b₂) (c₁, c₂)
  apply Quot.sound
  notation_simp
)

theorem MyInt.add_assoc (M N K : MyInt) :
    M + N + K = M + (N + K) := by
  revert M N K
  unfold_int₃
  ac_rfl

theorem MyInt.add_comm (M N : MyInt) : M + N = N + M := by
  revert M N
  unfold_int₂
  ac_rfl

-- MyInt の足し算が結合法則を満たすことを登録する
instance : Std.Associative (α := MyInt) (· + ·) where
  assoc := MyInt.add_assoc

-- MyInt の足し算が交換法則を満たすことを登録する
instance : Std.Commutative (α := MyInt) (· + ·) where
  comm := MyInt.add_comm

/-- 整数の引き算-/
def MyInt.sub (M N : MyInt) : MyInt := M + -N

/-- 引き算をA - B と書けるように型クラスに登録する -/
instance : Sub MyInt where
  sub := MyInt.sub

-- 後で使うので補題として登録しておく
@[simp, notation_simp]
theorem MyInt.sub_def (X Y : MyInt) : X - Y = X + -Y := rfl

theorem MyInt.neg_add_cancel (M : MyInt) : -M + M = 0 := by
  revert M
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
example (A B : MyInt) : (A + B) - B = A := by
  abel

example (A B C : MyInt) : (A - B) - C + B + C = A := by
  abel
