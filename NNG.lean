-- NNG と同じように、標準の Nat とは独立した教材用の自然数を使う。
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

attribute [pp_nodot] MyNat.succ

instance : Inhabited MyNat where
  default := MyNat.zero

-- `0`、`1`、`2` などの数値を MyNat として書けるようにする。
def ofNat : Nat → MyNat
  | Nat.zero => MyNat.zero
  | Nat.succ n => MyNat.succ (ofNat n)

-- 帰納法の `zero` と数値表記の `0` を定義上まったく同じものにする。
@[reducible] instance : OfNat MyNat 0 where
  ofNat := MyNat.zero

-- 0 以外の数値表記も使えるようにする。0 の場合とは重ならない。
@[reducible] instance {n : Nat} : OfNat MyNat (Nat.succ n) where
  ofNat := MyNat.ofNat (Nat.succ n)

theorem zero_eq_0 : MyNat.zero = 0 := rfl

-- 帰納法の基底ケースを、コンストラクタ `zero` ではなく
-- 普段使う数値表記 `0` で表示・証明できるようにする。
@[induction_eliminator, elab_as_elim]
def induction {motive : MyNat → Sort u}
    (zero : motive 0)
    (succ : ∀ n, motive n → motive (MyNat.succ n)) :
    ∀ n, motive n
  | MyNat.zero => zero
  | MyNat.succ n => succ n (induction zero succ n)

-- 定義を展開して計算できない、教材用の加算。
opaque add : MyNat → MyNat → MyNat

instance : Add MyNat where
  add := MyNat.add

/- ここから開始 -/

axiom one_eq_succ_zero : (1 : MyNat) = MyNat.succ 0
-- axiom two_eq_succ_one : (2 : MyNat) = MyNat.succ 1
-- axiom three_eq_succ_two : (3 : MyNat) = MyNat.succ 2
-- axiom four_eq_succ_three : (4 : MyNat) = MyNat.succ 3

axiom add_zero (n : MyNat) : n + 0 = n

axiom add_succ (a b : MyNat) : a + MyNat.succ b = MyNat.succ (a + b)

theorem succ_eq_add_one (n : MyNat) : MyNat.succ n = n + 1 := by
  rw [one_eq_succ_zero]
  rw [add_succ]
  rw [add_zero]

theorem zero_add (n : MyNat) : 0 + n = n := by
  induction n with
  | zero =>
    rw [add_zero]
  | succ n ih =>
    rw [add_succ]
    rw [ih]

theorem succ_add (a b : MyNat) : MyNat.succ a + b = MyNat.succ (a + b) := by
  induction b with
  | zero =>
    rw [add_zero, add_zero]
  | succ b ih =>
    rw [add_succ, add_succ]
    rw [ih]

theorem add_comm (a b : MyNat) : a + b = b + a := by
  induction b with
    | zero =>
      rw [add_zero, zero_add]
    | succ b ih =>
      rw [add_succ, succ_add]  -- symmetry
      rw [ih]
