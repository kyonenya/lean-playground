import LeanBook.Ch5_Mul_Macro
import LeanBook.NotationSimpTag

-- ## AddCancel

/-- MyNat の各コンストラクタの像は重ならない -/
example (n : MyNat) : MyNat.succ n ≠ MyNat.zero := by
  intro h
  injection h -- [帰納的に定義したものがもつ性質より従う]

/-- MyNat のコンストラクタは単射 -/
example (m n : MyNat) (h : MyNat.succ m = MyNat.succ n) : m = n := by
  injection h

example (m n : MyNat) (h : m + 1 = n + 1) : m = n := by
  injection h

-- 以降、l m n はすべてMyNat 型の項とする
variable {l m n : MyNat}

/-- 右から足す演算(· + m) は単射 -/
theorem MyNat.add_right_cancel (h : l + m = n + m) : l = n := by
  induction m with
  | zero =>
    simp only [add_zero] at h
    exact h
  | succ m ih =>
    have lem : (l + m) + 1 = (n + m) + 1 := calc
      _ = l + (m + 1) := by ac_rfl
      _ = n + (m + 1) := by rw [h]
      _ = (n + m) + 1 := by ac_rfl
    have : l + m = n + m := by
      injection h
    exact ih this

/-- 左から足す演算(l + ·) は単射-/
theorem MyNat.add_left_cancel (h : l + m = l + n) : m = n := by
  rw [MyNat.add_comm l m, MyNat.add_comm l n] at h
  apply MyNat.add_right_cancel h

/-- 右からの足し算のキャンセル -/
@[simp ↓ ] theorem MyNat.add_right_cancel_iff : l + m = n + m ↔ l = n := by
  constructor
  · apply MyNat.add_right_cancel
  · intro h
    rw [h]

/-- 左からの足し算のキャンセル -/
@[simp ↓ ] theorem MyNat.add_left_cancel_iff : l + m = l + n ↔ m = n := by
  constructor
  · apply MyNat.add_left_cancel
  · intro h
    rw [h]

@[simp] theorem MyNat.add_right_eq_self : m + n = m ↔ n = 0 := by
  constructor <;> intro h
  case mpr => simp_all
  case mp =>
    have h2 : m + n = m + 0 := by
      rw [h]
      simp only [add_zero]
    -- simp only [add_left_cancel_iff] at h2
    -- exact h2
    -- [hとゴールをsimpしたうえで一致させる]
    simpa [MyNat.add_zero] using h2

@[simp] theorem MyNat.add_left_eq_self : n + m = m ↔ n = 0 := by
  rw [MyNat.add_comm n m, MyNat.add_right_eq_self]

@[simp] theorem MyNat.self_eq_add_right : m = m + n ↔ n = 0 := by
  rw [eq_comm]
  exact MyNat.add_right_eq_self

@[simp] theorem MyNat.self_eq_add_left : m = n + m ↔ n = 0 := by
  rw [MyNat.add_comm, eq_comm]
  exact MyNat.add_right_eq_self

/-- 和がゼロなら両方がゼロ -/
theorem MyNat.eq_zero_of_add_eq_zero :
    m + n = 0 → m = 0 ∧ n = 0 := by
  intro h
  cases n with
  | zero =>
    simp_all only [ctor_eq_zero, add_zero, and_self]
  | succ n =>
    exfalso
    injection h -- succ n ≠ 0

theorem MyNat.add_eq_zero_of_eq_zero : m = 0 ∧ n = 0 → m + n = 0 := by
  intro h
  simp_all only [add_zero]

@[simp]
theorem MyNat.add_eq_zero_iff_eq_zero : m + n = 0 ↔ m = 0 ∧ n = 0 := by
  constructor <;> intro h
  · induction n with
    | zero =>
      simp_all only [add_zero, and_self]
    | succ n ih =>
      exfalso
      rw [← MyNat.add_assoc] at h
      injection h -- +1 して 0 にはならん
  · simp_all only [add_zero]

@[simp]
theorem MyNat.mul_eq_zero (m n : MyNat) : m * n = 0 ↔ m = 0 ∨ n = 0 := by
  constructor <;> intro h
  case mpr =>
    cases h <;> simp_all
  case mp =>
    induction n with
    | zero => simp_all only [mul_zero, or_true]
    | succ n ih =>
      left
      simp only [MyNat.mul_add, MyNat.mul_one] at h
      -- have : m * n + m = 0 := calc
      --   _ = m * (n + 1) := by distrib
      --   _ = 0 := by rw [h]
      simp_all only [add_eq_zero_iff_eq_zero]

example (n m : MyNat) : n + (1 + m) = n + 2 → m = 1 := by
  intro h
  simp_all only [↓MyNat.add_left_cancel_iff]
  rw [show 2 = 1 + 1 from rfl] at h -- 自作 distrib マクロはまだ h に対して適用できない
  simp_all only [↓MyNat.add_left_cancel_iff]

-- ## OrderDef

/-- 自然数上の広義の順序関係 ≤ -/
inductive MyNat.le (n : MyNat) : MyNat → Prop
  /-- ∀ n, n ≤ n -/
  | refl : MyNat.le n n
  /-- n ≤ m ならばn ≤ m + 1 -/
  | step {m : MyNat} : MyNat.le n m → MyNat.le n (m + 1)

/-- MyNat.le を≤で表せるようにする-/
instance : LE MyNat where
le := MyNat.le

example (m n : MyNat) (P : MyNat → MyNat → Prop) (h : m ≤ n) : P m n := by
  induction h with
  | refl =>
    guard_target =ₛ P m m
    sorry
  | @step n h ih =>
    guard_hyp ih : P m n
    guard_target =ₛ P m (n + 1)
    sorry

set_option linter.defProp false

/-- 帰納法を改善する -/
@[induction_eliminator]
def MyNat.le.recAux {n b : MyNat}
    {motive : (a : MyNat) → n ≤ a → Prop}
    (refl : motive n MyNat.le.refl)
    (step : ∀ {m : MyNat} (a : n ≤ m),
      motive m a → motive (m + 1) (MyNat.le.step a))
    (t : n ≤ b) :
  motive b t := by
  induction t with
  | refl => exact refl
  | @step c h ih =>
  exact step (a := h) ih

/-- 反射律 -/
theorem MyNat.le_refl (n : MyNat) : n ≤ n := by
  exact MyNat.le.refl

-- m, n, k は MyNat の項とする
variable {m n k : MyNat}

theorem MyNat.le_step (h : n ≤ m) : n ≤ m + 1 := by
  apply MyNat.le.step -- 逆向き適用：これを示せば十分
  exact h

/-- 推移律 -/
theorem MyNat.le_trans (hnm : n ≤ m) (hmk : m ≤ k) : n ≤ k := by
  induction hmk with
  | refl =>
    exact hnm
  | @step k hmk ih =>
    exact MyNat.le_step ih

-- 反射律を rfl で使える
attribute [refl] MyNat.le_refl

theorem MyNat.le_add_one_right (n : MyNat) : n ≤ n + 1 := by
  apply MyNat.le_step
  rfl

/-- 推移律を「推移的な二項関係 Trans」の型クラスとして登録する-/
instance : Trans (· ≤ · : MyNat → MyNat → Prop) (· ≤ ·) (· ≤ ·) where
trans := MyNat.le_trans

-- calc が使えるようになった
theorem MyNat.le_add_one_left (n : MyNat) : n ≤ 1 + n := calc
  _ ≤ n + 1 := by apply le_add_one_right
  _ = 1 + n := by ac_rfl

-- simp 属性に登録すると `(n ≤ n) ↔ True` といった同値の形をした書き換えルールに自動的に変換される
attribute [simp] MyNat.le_refl MyNat.le_add_one_right MyNat.le_add_one_left

-- ### 順序関係を和の等式に書き換える

/-- a ≤ b から証拠 k を含む等式を導く-/
theorem MyNat.le.dest (h : n ≤ m) : ∃ k, n + k = m := by
  induction h with
  | refl => exists 0
  | @step l h ih =>
    -- rcases-refine より obtain-exists のほうが楽だな……？
    -- rcases ih with ⟨t, ih⟩
    obtain ⟨t, ih⟩ := ih
    -- refine ⟨t + 1, ?_⟩
    exists t + 1
    rw [← ih]
    ac_rfl

theorem MyNat.le_add_right (n m : MyNat) : n ≤ n + m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [← MyNat.add_assoc n k]
    exact MyNat.le_step ih

/-- 和の等式から a ≤ b を導く -/
theorem MyNat.le.intro (h : n + k = m) : n ≤ m := by
  rw [← h]
  induction k with
  | zero => rfl
  | succ k ih =>
    apply MyNat.le_add_right

/-- 順序関係 n ≤ m を k の足し算で書き換える【頻出】 -/
theorem MyNat.le_iff_add : n ≤ m ↔ ∃ k, n + k = m := by
  constructor <;> intro h
  · exact MyNat.le.dest h
  · obtain ⟨k, hk⟩ := h
    exact MyNat.le.intro hk

example : 1 ≤ 4 := by
  rw [show 4 = 1 + 3 from rfl]
  apply MyNat.le_add_right

example : 1 ≤ 4 := by
  apply MyNat.le_step
  apply MyNat.le_step
  apply MyNat.le_step
  rfl

-- ## StrictOrder

/-- m < n を表す-/
def MyNat.lt (m n : MyNat) : Prop := (m + 1) ≤ n

/-- a < b という書き方ができるようにする-/
instance : LT MyNat where
  lt := MyNat.lt

example (m n : MyNat) : m < n ↔ (m + 1) ≤ n := by
  dsimp [(. < .)]
  dsimp [MyNat.lt]
  rfl

/-- 1 ≠ 0 が成り立つ-/
@[simp] theorem MyNat.one_neq_zero : 1 ≠ 0 := by
  intro h
  injection h

/-- 0 ≠ 1 が成り立つ-/
@[simp] theorem MyNat.zero_neq_one : 0 ≠ 1 := by
  intro h
  injection h

/-- 任意の自然数はゼロ以上である -/
@[simp] theorem MyNat.zero_le (n : MyNat) : 0 ≤ n := by
  rw [MyNat.le_iff_add]
  exists n
  simp only [zero_add]

/-- 0 以下の自然数は 0 しかない -/
theorem MyNat.zero_of_le_zero {n : MyNat} (h : n ≤ 0) : n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exfalso
    rw [MyNat.le_iff_add] at h
    obtain ⟨k, hk⟩ := h
    simp only [add_eq_zero_iff_eq_zero, one_neq_zero] at hk
    simp at hk

/-- 0 以下の自然数は 0 しかない -/
@[simp] theorem MyNat.le_zero {n : MyNat} : n ≤ 0 ↔ n = 0 := by
  constructor <;> intro h
  · exact MyNat.zero_of_le_zero h
  · rw [h]

/-- 任意の自然数はゼロか正 -/
theorem MyNat.eq_zero_or_pos (n : MyNat) : n = 0 ∨ 0 < n := by
  induction n with
  | zero => simp only [true_or]
  | succ n ih =>
    dsimp [(. < .), MyNat.lt] at *
    cases ih with
    | inl ih =>
      rw [ih]
      simp_all only [zero_add, one_neq_zero, le_refl, or_true]
    | inr ih =>
      simp_all only [zero_add, add_eq_zero_iff_eq_zero, one_neq_zero, and_false, false_or]
      exact MyNat.le_step ih

theorem MyNat.eq_or_lt_of_le {m n : MyNat} : n ≤ m → n = m ∨ n < m := by
  intro h
  dsimp [(. < .), MyNat.lt]
  rw [MyNat.le_iff_add] at *
  obtain ⟨t, ht⟩ := h
  induction t with
  | zero =>
    left
    simpa using ht
  | succ t _ =>
    right
    exists t
    -- rw [MyNat.add_assoc, MyNat.add_comm 1 t]
    -- exact ht
    -- [仮定は先に使ってしまえ！]
    rw [← ht]
    ac_rfl

/-- 【重要】狭義順序は広義順序よりも「強い」-/
theorem MyNat.le_of_lt {a b : MyNat} (h : a < b) : a ≤ b := by
  dsimp[(. < .), MyNat.lt] at h
  have : a ≤ b := calc
    _ ≤ a + 1 := by simp only [le_add_one_right]
    _ ≤ b := h
  assumption

theorem MyNat.le_of_eq_or_lt {m n : MyNat} : n = m ∨ n < m → n ≤ m := by
  intro h
  cases h with
  | inl h =>
    rw [h]
  | inr h =>
    exact MyNat.le_of_lt h

/-- 広義順序 ≤ は等号 = と狭義順序 < で書き換えられる -/
theorem MyNat.le_iff_eq_or_lt {m n : MyNat} : n ≤ m ↔ n = m ∨ n < m := by
  constructor
  · exact MyNat.eq_or_lt_of_le
  · exact MyNat.le_of_eq_or_lt

/-- 強力：すべての数は b より小さいか b 以上である -/
theorem MyNat.lt_or_ge (a b : MyNat) : a < b ∨ b ≤ a := by
-- a < b を定義に従いa + 1 ≤ b で書き換える
  dsimp [(· < ·), MyNat.lt]
  induction a with
  | zero =>
    simp_all only [zero_add, le_zero]
    have : b = 0 ∨ 0 < b := MyNat.eq_zero_or_pos b
    dsimp [(· < ·), MyNat.lt] at this
    cases this <;> simp_all
  | succ a ih =>
    cases ih with
    | inr h =>
      right
      exact MyNat.le_step h
    | inl h =>
      rw [MyNat.le_iff_eq_or_lt] at h
      -- = か < で場合分け
      cases h with
      | inl h =>
        right
        rw [h]
      | inr h =>
        dsimp [(· < ·), MyNat.lt] at h
        left
        exact h

theorem MyNat.lt_of_not_le {a b : MyNat} (h : ¬ a ≤ b) : b < a := by
  have : b < a ∨ a ≤ b := MyNat.lt_or_ge b a -- 強力な定理をいきなり補題にする
  cases this with
  | inl hc => assumption
  | inr hc => contradiction

-- 先に補題をやる
theorem MyNat.add_one_ne_lt (n : MyNat) : ¬ n + 1 ≤ n := by
  intro h
  rw [MyNat.le_iff_add] at h
  obtain ⟨k, hk⟩ := h
  rw [MyNat.add_assoc] at hk
  simp_all only [MyNat.add_right_eq_self, MyNat.add_eq_zero_iff_eq_zero, MyNat.one_neq_zero,
    false_and]

theorem MyNat.not_le_of_lt{a b : MyNat} (h : a < b) : ¬ b ≤ a := by
  intro hle
  dsimp [(· < ·), MyNat.lt] at h
  have hcontra : a + 1 ≤ a := MyNat.le_trans h hle
  exact MyNat.add_one_ne_lt a hcontra

theorem MyNat.lt_iff_le_not_le (a b : MyNat) : a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
  constructor <;> intro h
  case mp =>
    have hright : ¬ b ≤ a := MyNat.not_le_of_lt h
    have hleft : a ≤ b := MyNat.le_of_lt h
    exact ⟨hleft, hright⟩
  case mpr =>
    exact MyNat.lt_of_not_le h.right

theorem MyNat.le_total (a b : MyNat) : a ≤ b ∨ b ≤ a := by
  have : b < a ∨ a ≤ b := MyNat.lt_or_ge b a -- 強力な定理をいきなり補題にする
  cases this with
  | inl h =>
    -- [関数適用した結果を補題として持つ]
    -- replace h : b ≤ a := MyNat.le_of_lt h
    right
    -- [逆向き適用した結果と一致させる]
    apply MyNat.le_of_lt
    assumption
  | inr h =>
    left
    assumption

example (a : MyNat) : a ≠ a + 1 := by
  intro h
  simp_all only [MyNat.self_eq_add_right, MyNat.one_neq_zero]

theorem MyNat.lt_def (m n : MyNat) : m < n ↔ m + 1 ≤ n := by
  rfl

open Lean Parser Tactic

/-- + や ≤ など、演算子や記法を定義に展開する -/
syntax "notation_simp" (simpArgs)? (location)? : tactic

macro_rules
| `(tactic| notation_simp $[[$simpArgs,*]]? $[at $location]?) =>
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic| simp only [notation_simp, $args,*] $[at $location]?)

-- < の定義を展開する定理にnotation_simp 属性を付与する
attribute [notation_simp] MyNat.lt_def

section

open Lean Parser Tactic

/-- + や ≤ など、演算子や記法を定義に展開する -/
syntax "notation_simp?" (simpArgs)? (location)? : tactic
macro_rules
| `(tactic| notation_simp? $[[$simpArgs,*]]? $[at $location]?) =>
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic| simp? only [notation_simp, $args,*] $[at $location]?)
end

example (m n : MyNat) : m < n := by
  -- notation_simp?
  simp only [MyNat.lt_def]
  sorry
