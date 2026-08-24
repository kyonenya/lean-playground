import LeanBook.Ch5_Mul_Macro

-- ## AddCancel

/-- MyNat の各コンストラクタの像は重ならない -/
example (n : MyNat) : MyNat.succ n ≠ MyNat.zero := by
  intro h
  injection h -- 帰納的に定義したものがもつ性質より従う

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
