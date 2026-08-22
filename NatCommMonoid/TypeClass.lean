inductive MyNat where -- 帰納的定義
  | zero
  | succ (n : MyNat)

def MyNat.ofNat (n : Nat) : MyNat :=
  match n with
  | 0 => MyNat.zero
  | n + 1 => MyNat.succ (MyNat.ofNat n)

-- `OfNat` 型クラスの `インスタンス`
@[default_instance]
instance (n : Nat) : OfNat MyNat n where
  ofNat := MyNat.ofNat n
-- 文字 0, 1, 2... が使えるようになる

#check 0 -- MyNat

def MyNat.add (m n : MyNat) : MyNat :=
  -- 第二引数に対してパターンマッチ
  match n with
  | zero => m
  | succ n => succ (add m n)

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
    -- 普段登録されている simp ルールに加えて、今回だけ帰納法の仮定 ih も単純化ルールとして使ってくれ
    simp [ih]
