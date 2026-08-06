# lean-playground

Lean 4とMathlibの練習用プロジェクトです。

## 使い方

Leanファイルでは、次の1行でMathlibを利用できます。

```lean
import Mathlib
```

プロジェクト全体を確認するには、リポジトリのルートで実行します。

```sh
lake build
```

特定のファイルだけ確認する場合は、次のように実行します。

```sh
lake lean SetTheoryGame.lean
```
