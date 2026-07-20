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

---- Tutorial World ----

axiom one_eq_succ_zero : (1 : MyNat) = MyNat.succ 0
axiom two_eq_succ_one : (2 : MyNat) = MyNat.succ 1
axiom three_eq_succ_two : (3 : MyNat) = MyNat.succ 2
axiom four_eq_succ_three : (4 : MyNat) = MyNat.succ 3
axiom five_eq_succ_four : (5 : MyNat) = MyNat.succ 4

axiom add_zero (n : MyNat) : n + 0 = n

axiom add_succ (a b : MyNat) : a + MyNat.succ b = MyNat.succ (a + b)

theorem succ_eq_add_one (n : MyNat) : MyNat.succ n = n + 1 := by
  rw [one_eq_succ_zero]
  rw [add_succ]
  rw [add_zero]

---- Addition World ----

theorem zero_add (n : MyNat) : 0 + n = n := by
  induction n with
  | zero =>
    rw [add_zero]
  | succ n ih =>
    rw [add_succ]
    rw [ih]

theorem succ_add (a b : MyNat) :
  MyNat.succ a + b = MyNat.succ (a + b) := by
  induction b with
  | zero =>
    rw [add_zero, add_zero]
  | succ b ih =>
    rw [add_succ, add_succ] -- succ outside
    rw [ih]

theorem add_comm (a b : MyNat) :
  a + b = b + a := by
  induction b with
    | zero =>
      rw [add_zero, zero_add]
    | succ b ih =>
      rw [add_succ, succ_add] -- symmetry
      rw [ih]

theorem add_assoc (a b c : MyNat) :
  a + b + c = a + (b + c) := by
  induction c with
  | zero =>
    rw [add_zero, add_zero]
  | succ c ih =>
    rw [add_succ, add_succ, add_succ] -- succ outside
    rw [ih]

theorem add_right_com (a b c : MyNat) :
  (a + b) + c = (a + c) + b := by
  rw [add_assoc]
  rw [add_comm b c]
  rw [← add_assoc]

---- Implication World ----

theorem _apply_and_exact (x y : MyNat)
  (h1 : x = 37)
  (h2 : x = 37 → y = 42) :
  y = 42 := by
  have h3 : y = 42 := h2 h1 -- apply h2 at h1
  exact h3

/--
 - 必要なのが Y なら、`succ_inj h` のように X を渡す必要がある
 - 必要なのが X → Y なら、関数 `succ_inj` を引数省略で書ける
 -/
axiom succ_inj {a b : MyNat} :
  MyNat.succ a = MyNat.succ b → a = b

theorem _example_succ_inj (x : MyNat)
  (h : x + 1 = 4) :
  x = 3 := by
  rw [← succ_eq_add_one] at h
  rw [four_eq_succ_three] at h
  have h2 : x = 3 := succ_inj h
  exact h2

theorem _apply_backwards (x : MyNat)
  (h : x + 1 = 4) :
  x = 3 := by
  apply succ_inj -- this => x = 3
  rw [succ_eq_add_one, ← four_eq_succ_three]
  exact h

theorem _example_intro (x : MyNat) :
  x = 24 → x = 24 := by
  intro h
  exact h

theorem _apply_backwards_2 (x y : MyNat) :
  x + 1 = y + 1 → x = y := by
  intro h
  apply succ_inj
  repeat rw [succ_eq_add_one]
  exact h

theorem _eq_and_not_eq (x y : MyNat)
  (h1 : x = y)
  (h2 : x ≠ y) : -- x = y → False
  False := by
  -- have hf : False := h2 h1
  -- exact hf
  apply h2
  exact h1

/--
 - HOC
 - x → (0 = succ x) → False
 -/
axiom zero_ne_succ (x : MyNat) :
  0 ≠ succ x -- 0 = succ x → False

theorem zero_ne_one :
  (0 : MyNat) ≠ (1 : MyNat) := by -- 0 = 1 → False
  rw [one_eq_succ_zero]
  exact zero_ne_succ 0

theorem one_ne_zero :
  (1 : MyNat) ≠ 0 := by
  symm
  exact zero_ne_one

theorem _two_ne_three :
  2 + 2 ≠ (3 : MyNat) := by
  repeat rw [three_eq_succ_two, two_eq_succ_one, one_eq_succ_zero]
  repeat rw [add_succ]
  rw [add_zero]
  intro h
  have h2 : succ (succ (succ 0)) = succ (succ 0) := succ_inj h
  replace h2 : succ (succ 0) = succ 0 := succ_inj h2
  replace h2 : succ 0 = 0 := succ_inj h2
  symm at h2
  replace h2 : False := zero_ne_succ 0 h2 -- HOC
  exact h2
