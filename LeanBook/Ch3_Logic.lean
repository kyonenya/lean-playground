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
