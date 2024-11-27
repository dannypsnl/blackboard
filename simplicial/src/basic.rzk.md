```rzk
#lang rzk-1
```

```rzk
#def product
  ( A B : U)
  : U
  := Σ (x : A) , B

#def id
  ( A : U)
  ( x : A)
  : A := x
```
