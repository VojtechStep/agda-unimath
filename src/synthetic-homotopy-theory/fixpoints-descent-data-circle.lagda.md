# Fixpoints for descent data on the circle

```agda
module synthetic-homotopy-theory.fixpoints-descent-data-circle where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.descent-circle
```

</details>

## Idea

A fixpoint for [descent data](synthetic-homotopy-theory.descent-data-circle.md) `(X , e)` for the [circle](synthetic-homotopy-theory.circle.md) consists of an element `x : X` equipped with an identification `e x ＝ x`.

## Definitions

### Fixpoints of descent data

A fixpoint of `(X, e)` is a fixpoint of `e`.

```agda
fixpoint-descent-data-circle :
  { l1 : Level}
  ( P : descent-data-circle l1) → UU l1
fixpoint-descent-data-circle P =
  Σ ( type-descent-data-circle P)
    ( λ x → map-aut-descent-data-circle P x ＝ x)
```
