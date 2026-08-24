import LeanBook.Ch2_MyNat

-- ## TypeClass

-- `OfNat` 型クラスの `インスタンス`
@[default_instance]
instance (n : Nat) : OfNat MyNat n where
  ofNat := MyNat.ofNat n
-- 文字 0, 1, 2... が使えるようになる

-- [記号そのものはLeanが知っているけれど、その型で何を意味するかはインスタンス次第]
instance : Add MyNat where
  add := MyNat.add

#eval 1 + 2 -- succ(succ(succ 0))
#check fun n => n + 1

-- 表示だけLean組み込みの自然数にする
def MyNat.toNat (n : MyNat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => MyNat.toNat n + 1

-- `Repr` 型クラス：出力方式を指定する
instance : Repr MyNat where
  reprPrec n _ := repr n.toNat

#eval 0 + 1

example (n : MyNat) : n + 0 = n := by -- match m with zero => n
  rfl

#reduce fun (n : MyNat) => n + 0 -- n ↦ n
#reduce fun (n : MyNat) => 0 + n

set_option pp.fieldNotation.generalized false in

theorem MyNat.add_zero (n : MyNat) :
  n + 0 = n := by
  rfl

theorem MyNat.add_succ (m n : MyNat) :
  m + .succ n = .succ (m + n) := by
  rfl

-- ## Induction

theorem MyNat.zero_add (n : MyNat) : 0 + n = n := by
  induction n with
  | zero =>
    guard_target =ₛ 0 + MyNat.zero = MyNat.zero
    rfl
  |succ n' ih
  guard_target =ₛ 0 + MyNat.succ n' = MyNat.succ n'
  guard_hyp ih : 0 + n' = n'
  rw [MyNat.add_succ]
  rw [ih]

example (n : MyNat) :
  1 + n = .succ n := by
  induction n with
  | zero =>
    rfl
  | succ m ih =>
    rw [MyNat.add_succ]
    rw [ih]

-- ## Simp

example (n : MyNat) : 0 + (n + 0) = n := by
  -- 最初はsimp で証明できない
  fail_if_success simp
  -- 明示的にrw で証明する
  rw [MyNat.add_zero, MyNat.zero_add]

attribute [simp] MyNat.add_zero MyNat.zero_add

example (n : MyNat) : 0 + (n + 0) = n := by
  simp

/-- MyNat において 0 はzero だと解釈される-/
theorem MyNat.ctor_eq_zero : MyNat.zero = 0 := by
  rfl

example : MyNat.zero = 0 := by
  -- simp に手動で命題を渡しても証明できる
  simp [MyNat.ctor_eq_zero]

attribute [simp] MyNat.ctor_eq_zero
attribute [simp] MyNat.add_succ

example (m n : MyNat) (h : m + n + 0 = n + m) : m + n = n + m := by
  -- simp at 仮定 or *(全て)
  simp only [MyNat.add_zero] at h
  guard_hyp h : m + n = n + m
  exact h

example (m n : MyNat) (h : m + 0 = n) : (m + 0) + 0 = n := by
  -- すべての仮定とゴールをこれ以上単純化できなくなるまで単純化
  simp_all

/-- 左のオペランドに付いた.succ は外側に出せる-/
@[simp] theorem MyNat.succ_add (m n : MyNat) : .succ m + n = .succ (m + n) := by
  induction n with
  | zero => rfl
  -- simp? で使う証明だけ表示できる
  -- | succ m ih => simp? [ih]
  | succ m ih => simp only [add_succ, ih]

example (n : MyNat) : 2 + n = n + 2 := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    -- [普段登録されているsimpルールに加えて、今回だけ帰納法の仮定ihも使ってくれ]
    simp [ih]

-- ## AcRfl

theorem MyNat.add_comm (m n : MyNat) : m + n = n + m := by
  induction n with
  | zero =>
    simp only [ctor_eq_zero, add_zero, zero_add]
  | succ n' ih =>
    simp only [add_succ, succ_add, succ.injEq]
    exact ih

-- [inductionの帰納型から自動生成される補題]
#check MyNat.succ.injEq -- (n.succ = m.succ) = (n = m)
#check MyNat.noConfusion -- zero ≠ succ n

theorem MyNat.add_assoc (l m n : MyNat) : l + m + n = l + (m + n) := by
  induction n with
  -- | zero => simp only [ctor_eq_zero, add_zero]
  -- 第二引数が 0 なので足し算の定義から従う
  | zero => rfl
  | succ n ih =>
    simp only [add_succ, succ.injEq]
    exact ih

-- `ac_rfl` というタクティクに結合・交換法則を登録する
instance : Std.Associative (α := MyNat) (· + ·) where
  assoc := MyNat.add_assoc
instance : Std.Commutative (α := MyNat) (· + ·) where
  comm := MyNat.add_comm

example (l m n : MyNat) : l + m + n + 3 = m + (l + n) + 3 := by
  ac_rfl

example (l m n : MyNat) : l + (1 + m) + n = m + (l + n) + 1 := by
  ac_rfl

-- ## BetterInduction

/-- 帰納法を見やすくする
- MyNat.zero → 0
- MyNat.succ → +1
-/
def MyNat.recAux.{u} {motive : MyNat → Sort u}
  (zero : motive 0)
  (succ : (n : MyNat) → motive n → motive (n + 1)) (t : MyNat) : motive t :=
  match t with
  | .zero => zero
  | .succ n => succ n (MyNat.recAux zero succ n)

attribute [induction_eliminator] MyNat.recAux
