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

-- set_option pp.fieldNotation.generalized false in

-- example (n : MyNat) : 0 + n = n := by
--   induction n with
--   | zero =>
