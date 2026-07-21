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

instance instOfNat {n : Nat} : OfNat MyNat n where
  ofNat := MyNat.ofNat n

theorem zero_eq_0 : MyNat.zero = 0 := rfl

/-- `MyNat`の正の数値を1段の`succ`として展開する。 -/
theorem ofNat_succ {n : Nat} :
    (OfNat.ofNat (Nat.succ n) : MyNat) =
      MyNat.succ (OfNat.ofNat n) := rfl

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

/-- succ outside -/
axiom add_succ (a b : MyNat) : a + succ b = succ (a + b)

theorem succ_eq_add_one (n : MyNat) : succ n = n + 1 := by
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

/-- implicit args -/
axiom succ_inj {a b : MyNat} :
  succ a = succ b → a = b

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

example (x : MyNat) :
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

---- Advanced Addition World ----

theorem add_right_cancel (a b n : MyNat)
  (h1 : a + n = b + n) :
  a = b := by
  induction n with
  | zero =>
    rw [add_zero, add_zero] at h1
    exact h1
  | succ n ih =>
    rw [add_succ, add_succ] at h1
    have h2 : a + n = b + n := succ_inj h1
    exact ih h2

theorem add_left_cancel (a b n : MyNat)
  (h1 : n + a = n + b) :
  a = b := by
  repeat rw [add_comm n] at h1
  exact add_right_cancel a b n h1

theorem add_left_eq_self (x y : MyNat)
  (h1 : x + y = y) :
  x = 0 := by
  conv at h1 =>
    rhs
    rw [← zero_add y]
  exact add_right_cancel x 0 y h1

theorem add_right_eq_self (x y : MyNat)
  (h1 : x + y = x) :
  y = 0 := by
  rw [add_comm] at h1
  exact add_left_eq_self y x h1

---- Algorithm World ----

theorem add_left_comm (a b c : MyNat) :
  a + (b + c) = b + (a + c) := by
  rw [← add_assoc]
  rw [add_comm a b]
  rw [add_assoc]

theorem _example_comm (x y z w : MyNat) :
  x + y + (z + w) = x + z + w + y := by
  repeat rw [add_assoc] -- blacket all
  rw [add_left_comm y z /-w-/]
  rw [add_comm y w]

theorem _example_simp {b c d f h g e} (a : MyNat) :
  d + f + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp only [add_left_comm, add_comm]

-- macro "simp_add" : tactic => `(tactic|(
  -- simp only [add_assoc, add_left_comm, add_comm]))
macro "simp_add" : tactic =>
  `(tactic| simp only [add_assoc, add_left_comm, add_comm])

theorem _example_simp_2 {b c d f h g e} (a : MyNat) :
  d + f + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp_add

def pred : MyNat → MyNat
  | 0 => 0 -- precisely 'none'
  | succ n => n

axiom pred_succ (n: MyNat) :
  pred (succ n) = n

theorem _succ_inj_proof (a b : MyNat)
  (h : succ a = succ b) :
  a = b := by
  rw [← pred_succ a]
  rw [h]
  rw [pred_succ]

/-- 述語：命題が返ってくる関数 -/
def is_zero : MyNat → Prop
  | 0 => True
  | succ _n => False

theorem is_zero_zero :
  is_zero 0 = True := by
  rfl

theorem is_zero_succ (n : MyNat) :
  is_zero (succ n) = False := by
  rfl

theorem succ_ne_zero (n : MyNat) :
  succ n ≠ 0 := by
  intro h
  rw [← is_zero_succ n]
  rw [h]
  rw [is_zero_zero]
  trivial

theorem succ_ne_succ (m n : MyNat)
  (h : m ≠ n) :
  succ m ≠ succ n := by
  intro heq
  have heq2 : m = n := succ_inj heq
  -- exact h heq2 -- m = n, m ≠ n
  rw [heq2] at h
  apply h -- (m = n) → False
  rfl

instance instDecidableEq : DecidableEq MyNat
  | 0, 0 => isTrue <| by
      rfl
  | succ m, 0 => isFalse <| by
      exact succ_ne_zero m
  | 0, succ n => isFalse <| by
      exact zero_ne_succ n
  | succ m, succ n =>
      match instDecidableEq m n with
      | isTrue h => isTrue <| by
          rw [h]
      | isFalse h => isFalse <| by
          exact succ_ne_succ m n h

macro "decide" : tactic => `(tactic|(
  try simp only [ofNat_succ, zero_eq_0, add_zero, add_succ]
  try decide
))

example : (20 : MyNat) + 20 = 40 := by
  decide

example : (2 : MyNat) + 2 ≠ 5 := by
  decide
