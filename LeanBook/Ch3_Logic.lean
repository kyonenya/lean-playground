

-- ## 全称量化 ∀

def P (n : Nat) : Prop := n = n

example : ∀ a : Nat, P a := by
  -- x : Nat が任意に与えられたとする
  intro x
  -- P を展開すればあきらか
  -- dsimp：定義への展開
  dsimp [P]

/-- すべての自然数x についてP x が成り立つなら、P 0 も成り立つ-/
example (P : Nat → Prop) (h : ∀ x : Nat, P x) : P 0 := by
  -- 全称量化に任意の値で呼び出す
  exact h 0

-- ## 存在量化 ∃

/-- 偶数であることを表す述語-/
def even (n : Nat) : Prop := ∃ m : Nat, n = m + m

/-- 4 : Nat は偶数-/
example : even 4 := by
  -- その述語を成り立たせるような具体的なxを与える
  exists 2

example (α : Type) (P Q : α → Prop) (h : ∃ x : α, P x ∧ Q x)
: ∃ x : α, Q x := by
  -- 仮定 h が存在を主張している y を取り出す
  obtain ⟨y, hy⟩ := h
  exists y
  exact hy.right

-- ## 同値 ↔

example (P Q : Prop) (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by
  constructor
  · exact h1
  · exact h2

/-- [constructorタクティクを使用した場合は、かなりの頻度で、その直後にintroタクティクを使うことになります] -/
example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  constructor
  case mp =>
    intro h
    exact h hq
  case mpr =>
    intro hp hq
    exact hp

/-- [<;>は直前のタクティクで生成されたすべてのゴールに対して後続のタクティクを適用します] -/
example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  constructor <;> intro h
  case mp => exact h hq
  case mpr =>
    intro hq
    exact h

/-- 同値な命題同士は書き換え可能 -/
example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  rw [← h]
  exact hp

-- ## 論理和 ∨

-- left / right で決め打ち
example (P Q : Prop) (hp : P) : P ∨ Q := by
  left
  exact hp

-- cases で場合分け
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp =>
    right
    exact hp
  | inr hp =>
    left
    exact hp

example (P Q : Prop) : (¬ P ∨ Q) → (P → Q) := by
  intro h h2
  cases h with
  | inr hp =>
    exact hp
  | inl hp =>
    contradiction
