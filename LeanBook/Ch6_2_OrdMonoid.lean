import LeanBook.Ch6_1_Order
import LeanBook.CompatibleTag

variable {a b m n : MyNat}

/-- 足し算(l + ·) は順序関係を保つ-/
theorem MyNat.add_le_add_left (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
  rw [MyNat.le_iff_add] at *
  obtain ⟨k, hk⟩ := h
  exists k
  rw [← hk]
  ac_rfl

/-- 足し算(· + l) は順序関係を保つ-/
theorem MyNat.add_le_add_right (h : m ≤ n) (l : MyNat) : m + l ≤ n + l := by
  rw [MyNat.add_comm m l, MyNat.add_comm n l]
  -- exact MyNat.add_le_add_left h l
  -- [assumption=名前を知らずにexactしたいときの道具]
  -- apply MyNat.add_le_add_left -- m ≤ n
  -- assumption
  apply MyNat.add_le_add_left <;> assumption

theorem MyNat.add_le_add (h1 : m ≤ n) (h2 : a ≤ b) : m + a ≤ n + b := calc
  _ ≤ n + a := MyNat.add_le_add_right h1 a
  _ ≤ n + b := MyNat.add_le_add_left h2 n

example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
  apply MyNat.add_le_add_left <;> assumption -- よしなに仮定を探してきて関数に与える

/-- 関係 a ∼ b が成り立つなら f a ∼ f b が成り立つ、というタイプの推論を行う -/
syntax "compatible" : tactic

section
  local macro_rules
  | `(tactic| compatible) =>
    `(tactic| apply MyNat.add_le_add_left <;> assumption)

  local macro_rules
  | `(tactic| compatible) =>
    `(tactic| apply MyNat.add_le_add_right <;> assumption)

  local macro_rules
  | `(tactic| compatible) => `(tactic| apply MyNat.add_le_add <;> assumption)

  example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
    compatible

  example (h : m ≤ n) (l : MyNat) : m + l ≤ n + l := by
    compatible

  example (h1 : m ≤ n) (h2 : a ≤ b) : m + a ≤ n + b := by
    compatible

end

open Lean Elab Tactic in
/-- 関係 a ∼ b が成り立つなら f a ∼ f b が成り立つ、というタイプの推論を行う -/
elab "compatible" : tactic => do
  -- [compatible] 属性が付与された定理をリストアップする
  let taggedDecls ← labelled `compatible
  if taggedDecls.isEmpty then
    throwError "`[compatible]`が付与された定理はありません。"
  for decl in taggedDecls do
    let declStx := mkIdent decl
    try
      -- [compatible] 属性が付与された定理 thm に対して apply thm <;> assumption を試す
      evalTactic <| ← `(tactic| apply $declStx <;> assumption)

      -- 成功したら終了する
      return ()
    catch _ =>
      -- 失敗したら単に次の候補に進む
      pure ()
  throwError "ゴールを閉じることができませんでした。"

attribute [compatible] MyNat.add_le_add_left
  MyNat.add_le_add_right MyNat.add_le_add

example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
  compatible

example (h : m ≤ n) (l : MyNat) : m + l ≤ n + l := by
  compatible

example (h1 : m ≤ n) (h2 : a ≤ b) : m + a ≤ n + b := by
  compatible

-- ### 足し算は狭義順序を保つ

@[compatible]
theorem MyNat.add_lt_add_left {m n : MyNat} (h : m < n) (k : MyNat)
    : k + m < k + n := by
  notation_simp at *
  rw [MyNat.add_assoc]
  compatible

@[compatible]
theorem MyNat.add_lt_add_right {m n : MyNat} (h : m < n) (k : MyNat)
    : m + k < n + k := by
  notation_simp at *
  rw [MyNat.add_assoc, MyNat.add_comm k 1, ← MyNat.add_assoc]
  compatible

-- ### 順序についても足し算はキャンセル可能

section

variable (m n k : MyNat)

theorem MyNat.le_of_add_le_add_left : k + m ≤ k + n → m ≤ n := by
  intro h
  rw [MyNat.le_iff_add] at *
  obtain ⟨d, hd⟩ := h
  exists d
  rw [MyNat.add_assoc] at hd
  simp only [add_left_cancel_iff] at hd
  exact hd

theorem MyNat.le_of_add_le_add_right : m + k ≤ n + k → m ≤ n := by
  intro h
  rw [MyNat.add_comm m k, MyNat.add_comm n k] at h
  exact MyNat.le_of_add_le_add_left m n k h

/-- ≤ での足し算キャンセル -/
@[simp] theorem MyNat.add_le_add_iff_left : k + m ≤ k + n ↔ m ≤ n := by
  constructor
  -- · exact MyNat.le_of_add_le_add_left m n k h
  · apply MyNat.le_of_add_le_add_left
  · intro h
    compatible

/-- ≤ での足し算キャンセル -/
@[simp] theorem MyNat.add_le_add_iff_right : m + k ≤ n + k ↔ m ≤ n := by
  constructor
  · apply MyNat.le_of_add_le_add_right
  · intro h
    compatible

variable (m₁ m₂ n₁ n₂ l₁ l₂ : MyNat)
example (h1 : m₁ ≤ m₂) (h2 : n₁ ≤ n₂) (h3 : l₁ ≤ l₂)
    : l₁ + m₁ + n₁ ≤ l₂ + n₂ + m₂ := calc
  _ = l₁ + n₁ + m₁ := by ac_rfl
  _ ≤ l₁ + n₁ + m₂ := by compatible
  _ ≤ l₂ + n₁ + m₂ := by simp_all only [MyNat.add_le_add_iff_right]
  _ ≤ l₂ + n₂ + m₂ := by simp_all only [MyNat.add_le_add_iff_right,
    MyNat.add_le_add_iff_left]

-- ### a ≤ b → b ≤ a → a = b を示す

variable {n m k : MyNat}
theorem MyNat.lt_trans (h₁ : n < m) (h₂ : m < k) : n < k := by
  notation_simp at *
  have : n + 1 ≤ k := calc
    _ ≤ m := by exact h₁
    _ ≤ m + 1 := by simp only [le_add_one_right]
    _ ≤ k := by exact h₂
  exact this

theorem MyNat.lt_of_le_of_lt (h₁ : n ≤ m) (h₂ : m < k) : n < k := by
  notation_simp at *
  have : n + 1 ≤ k := calc
    _ ≤ m + 1 := by compatible
    _ ≤ k := by exact h₂
  exact this

theorem MyNat.lt_of_lt_of_le (h₁ : n < m) (h₂ : m ≤ k) : n < k := by
  notation_simp at *
  have : n + 1 ≤ k := calc
    _ ≤ m := by exact h₁
    _ ≤ k := by exact h₂
  assumption

instance : Trans (· < · : MyNat → MyNat → Prop) (· < ·) (· < ·) where
  trans := MyNat.lt_trans
instance : Trans (· ≤ · : MyNat → MyNat → Prop) (· < ·) (· < ·) where
  trans := MyNat.lt_of_le_of_lt
instance : Trans (· < · : MyNat → MyNat → Prop) (· ≤ ·) (· < ·) where
  trans := MyNat.lt_of_lt_of_le

/-- 狭義順序では反射律の否定が成り立つ。つまり ¬ (n < n) -/
@[simp]
theorem MyNat.lt_irrefl (n : MyNat) : ¬ n < n := by
  intro h
  notation_simp at h
  rw [MyNat.le_iff_add] at h
  obtain ⟨k, hk⟩ := h
  rw [MyNat.add_assoc] at hk
  simp only [add_right_eq_self, add_eq_zero_iff_eq_zero, one_neq_zero, false_and] at hk

/-- 反対称律は、非反射律 ¬ n < n に帰着する形で示せます -/
theorem MyNat.le_antisymm (h₁ : n ≤ m) (h₂ : m ≤ n) : n = m := by
  induction h₁ with
  | refl => rfl
  | @step p h ih =>
    exfalso
    have : n < n := calc
      _ ≤ p := by exact h
      _ < p + 1 := by notation_simp; rfl
      _ ≤ n := by exact h₂
    simp only [lt_irrefl] at this

example (a b : MyNat) : a < b ∨ a = b → a ≤ b := by
  intro h
  cases h with
  | inl h =>
    exact MyNat.le_of_lt h
  | inr h => simp only [MyNat.le_refl, h]
