# Zigzags between sequential diagrams

```agda
module synthetic-homotopy-theory.zigzags-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.identity-types

open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-homotopies
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.functoriality-sequential-colimits
open import synthetic-homotopy-theory.morphisms-sequential-diagrams
open import synthetic-homotopy-theory.sequential-colimits
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.shifts-sequential-diagrams
open import synthetic-homotopy-theory.universal-property-sequential-colimits
```

</details>

## Idea

A {{#concept "zigzag" Disambiguation="sequential diagrams"}} between
[sequential diagrams](synthetic-homotopy-theory.sequential-diagrams.md)
is a pair of families of maps and coherences between them, such that they fit
in the following diagram:

```text
  A₀ -----> A₁ -----> A₂ -----> ⋯
   \       ^ \       ^
    \     /   \     /
     \   /     \   /
      V /       V /
      B₀ -----> B₁ -----> ⋯
```

## Definitions

### A zigzag between sequential diagrams

```agda
module _
  {l1 l2 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  where

  zigzag-sequential-diagrams : UU (l1 ⊔ l2)
  zigzag-sequential-diagrams =
    Σ ( (n : ℕ) →
        family-sequential-diagram A n → family-sequential-diagram B n)
      ( λ f →
        Σ ( (n : ℕ) →
            family-sequential-diagram B n →
            family-sequential-diagram A (succ-ℕ n))
          ( λ g →
            Σ ( (n : ℕ) →
                coherence-triangle-maps
                  ( map-sequential-diagram A n)
                  ( g n)
                  ( f n))
              ( λ H →
                (n : ℕ) →
                coherence-triangle-maps
                  ( map-sequential-diagram B n)
                  ( f (succ-ℕ n))
                  ( g n))))
--             Σ ( (n : ℕ) →
--                 coherence-triangle-maps'
--                   ( map-sequential-diagram A n)
--                   ( g n)
--                   ( f n))
--               ( λ H →
--                 ( n : ℕ) →
--                 coherence-triangle-maps
--                   ( map-sequential-diagram B n)
--                   ( f (succ-ℕ n))
--                   ( g n))))
```

## Properties

### A zigzag between sequential diagrams may be shifted

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  (z : zigzag-sequential-diagrams A B)
  where

  shift-zigzag-sequential-diagram :
    zigzag-sequential-diagrams B (shift-sequential-diagram A)
  pr1 shift-zigzag-sequential-diagram = pr1 (pr2 z)
  pr1 (pr2 shift-zigzag-sequential-diagram) n = pr1 z (succ-ℕ n)
  pr1 (pr2 (pr2 shift-zigzag-sequential-diagram)) =
    pr2 (pr2 (pr2 z))
  pr2 (pr2 (pr2 shift-zigzag-sequential-diagram)) n =
    pr1 (pr2 (pr2 z)) (succ-ℕ n)
--   pr1 shift-zigzag-sequential-diagram = pr1 (pr2 z)
--   pr1 (pr2 shift-zigzag-sequential-diagram) n = pr1 z (succ-ℕ n)
--   pr1 (pr2 (pr2 shift-zigzag-sequential-diagram)) n =
--     inv-htpy (pr2 (pr2 (pr2 z)) n)
--   pr2 (pr2 (pr2 shift-zigzag-sequential-diagram)) n =
--     inv-htpy (pr1 (pr2 (pr2 z)) (succ-ℕ n))
```

-- ### A zigzag between sequential diagrams composes into a morphism between sequential diagrams

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  (z : zigzag-sequential-diagrams A B)
  where

  naturality-hom-zigzag-sequential-diagram :
    naturality-hom-sequential-diagram A B (pr1 z)
  naturality-hom-zigzag-sequential-diagram n =
    ( pr2 (pr2 (pr2 z)) n ·r (pr1 z n)) ∙h
    ( pr1 z (succ-ℕ n) ·l inv-htpy (pr1 (pr2 (pr2 z)) n))

  hom-zigzag-sequential-diagram : hom-sequential-diagram A B
  pr1 hom-zigzag-sequential-diagram = pr1 z
  pr2 hom-zigzag-sequential-diagram = naturality-hom-zigzag-sequential-diagram

  naturality-hom-shift-zigzag-sequential-diagram :
    naturality-hom-sequential-diagram B
      ( shift-sequential-diagram A)
      ( pr1 (pr2 z))
  naturality-hom-shift-zigzag-sequential-diagram n =
    ( pr1 (pr2 (pr2 z)) (succ-ℕ n) ·r (pr1 (pr2 z) n)) ∙h
    ( pr1 (pr2 z) (succ-ℕ n) ·l inv-htpy (pr2 (pr2 (pr2 z)) n))

  hom-shift-zigzag-sequential-diagram :
    hom-sequential-diagram B (shift-sequential-diagram A)
  pr1 hom-shift-zigzag-sequential-diagram = pr1 (pr2 z)
  pr2 hom-shift-zigzag-sequential-diagram =
    naturality-hom-shift-zigzag-sequential-diagram

  htpy-hom-zigzag-shift-zigzag-sequential-diagram :
    htpy-hom-sequential-diagram
      ( shift-sequential-diagram A)
      ( hom-shift-sequential-diagram A)
      ( comp-hom-sequential-diagram
        ( A)
        ( B)
        ( shift-sequential-diagram A)
        ( hom-shift-zigzag-sequential-diagram)
        ( hom-zigzag-sequential-diagram))
  pr1 htpy-hom-zigzag-shift-zigzag-sequential-diagram =
    pr1 (pr2 (pr2 z))
  pr2 htpy-hom-zigzag-shift-zigzag-sequential-diagram n =
    ( left-whisk-htpy-coherence-triangle-homotopies
      ( map-sequential-diagram A (succ-ℕ n) ·l inv-htpy (pr1 (pr2 (pr2 z)) n))
      ( pr1 (pr2 (pr2 z)) (succ-ℕ n) ·r map-sequential-diagram A n)
      ( inv-htpy
        ( ( ap-concat-htpy
            ( map-sequential-diagram A (succ-ℕ n) ·l (pr1 (pr2 (pr2 z)) n))
            ( left-whisk-inv-htpy
              ( map-sequential-diagram A (succ-ℕ n))
              ( pr1 (pr2 (pr2 z)) n))) ∙h
          ( right-inv-htpy
            ( ( map-sequential-diagram A (succ-ℕ n)) ·l
              ( pr1 (pr2 (pr2 z)) n)))))) ∙h
    ( ap-concat-htpy
      ( map-sequential-diagram A (succ-ℕ n) ·l (pr1 (pr2 (pr2 z)) n))
      ( inv-htpy
        ( pasting-coherence-squares-collapse-triangles
          ( map-sequential-diagram A n)
          ( pr1 z n)
          ( pr1 z (succ-ℕ n))
          ( map-sequential-diagram B n)
          ( pr1 (pr2 z) n)
          ( pr1 (pr2 z) (succ-ℕ n))
          ( map-sequential-diagram A (succ-ℕ n))
          ( inv-htpy (pr1 (pr2 (pr2 z)) n))
          ( pr2 (pr2 (pr2 z)) n)
          ( inv-htpy (pr2 (pr2 (pr2 z)) n))
          ( pr1 (pr2 (pr2 z)) (succ-ℕ n))
          ( left-inv-htpy (pr2 (pr2 (pr2 z)) n)))))

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : sequential-diagram l1} {B : sequential-diagram l2}
  {X : UU l3} {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  {Y : UU l4} {c' : cocone-sequential-diagram B Y}
  (up-c' : universal-property-sequential-colimit c')
  (z : zigzag-sequential-diagrams A B)
  where

  map-sequential-colimit-zigzag-sequential-diagram : X → Y
  map-sequential-colimit-zigzag-sequential-diagram =
    map-sequential-colimit-hom-sequential-diagram up-c c'
      ( hom-zigzag-sequential-diagram z)

  map-sequential-colimit-shift-zigzag-sequential-diagram : Y → X
  map-sequential-colimit-shift-zigzag-sequential-diagram =
    map-sequential-colimit-hom-sequential-diagram
      ( up-c')
      ( cocone-shift-sequential-diagram A c)
      ( hom-shift-zigzag-sequential-diagram z)

  is-equiv-map-sequential-colimit-zigzag-sequential-diagram :
    is-equiv map-sequential-colimit-zigzag-sequential-diagram
  is-equiv-map-sequential-colimit-zigzag-sequential-diagram =
    is-equiv-left-is-equiv-top-is-equiv-bottom-square
      ( map-sequential-colimit-zigzag-sequential-diagram)
      ( map-sequential-colimit-zigzag-sequential-diagram) -- really?
      ( map-sequential-colimit-shift-zigzag-sequential-diagram)
      ( ?)
      -- ( inv-htpy (hjk up-c) ∙h
      --   inv-htpy
      --     ( htpy-map-sequential-colimit-htpy-hom-sequential-diagram
      --       ( up-c)
      --       ( cocone-shift-sequential-diagram A c)
      --       ( htpy-hom-zigzag-shift-zigzag-sequential-diagram z)) ∙h
      --   [u])
      ( {!!})
      ( is-equiv-id)
      ( is-equiv-id)
    where
      [u] : map-sequential-colimit-hom-sequential-diagram up-c
             (cocone-shift-sequential-diagram A c)
             (comp-hom-sequential-diagram A B
              (shift-sequential-diagram A)
              (hom-shift-zigzag-sequential-diagram z)
              (hom-zigzag-sequential-diagram z))
             ~
             map-sequential-colimit-shift-zigzag-sequential-diagram
             ∘
             map-sequential-colimit-zigzag-sequential-diagram
      [u] =
        preserves-comp-map-sequential-colimit-hom-sequential-diagram
          ( up-c)
          ( up-c')
          ( cocone-shift-sequential-diagram A c)
          ( hom-shift-zigzag-sequential-diagram z)
          ( hom-zigzag-sequential-diagram z)
      [v] :
        htpy-hom-sequential-diagram
          ( shift-sequential-diagram B)
          ( hom-shift-sequential-diagram B)
          ( comp-hom-sequential-diagram
            B
            (shift-sequential-diagram A)
            (shift-sequential-diagram B)
            (shift-hom-sequential-diagram
              ( B)
              ( hom-zigzag-sequential-diagram z))
            (hom-shift-zigzag-sequential-diagram z))
      [v] =
        htpy-hom-zigzag-shift-zigzag-sequential-diagram
          ( shift-zigzag-sequential-diagram z)
```
