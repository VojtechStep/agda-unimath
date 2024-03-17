# Operations on cocones under span diagrams

```agda
module synthetic-homotopy-theory.operations-cocones-under-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences-arrows
open import foundation.equivalences-span-diagrams
open import foundation.function-extensionality
open import foundation.morphisms-arrows
open import foundation.morphisms-span-diagrams
open import foundation.operations-span-diagrams
open import foundation.span-diagrams
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-squares-of-maps
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types

open import synthetic-homotopy-theory.cocones-under-span-diagrams
```

</details>

## Idea

There are several ways of producing
[cocones under span diagrams](synthetic-homotopy-theory.cocones-under-span-diagrams.md)
by combining cocones with other cocones,
[morphisms of arrows](foundation.morphisms-arrows.md),
[equivalences of arrows](foundation.equivalences-arrows.md),
[morphisms of span diagrams](foundation.morphisms-span-diagrams.md),
[equivalences of span diagrams](foundation.equivalences-span-diagrams.md), and
so on.

## Definitions

### Horizontal composition of cocones under span diagrams

Consider a span diagram `s := A <-f- S -g-> B` and a moprhism `h : B → C`. Then
we can **compose** any cocone `c := (i , j , H)` with codomain `X` under the
span diagram `𝒮` **on the left** with a cocone `d` under the span diagram
`X <-j- B -h-> C` as indicated in the diagram

```text
        g       h
    S ----> B ----> C
    |       |       |
  f |       | j     | j'
    v       v       v
    A ----> X ----> Y
        i       i'
```

to obtain a cocone `(i'' , j'' , H'')` under the span diagram
`A <-f- S -h∘g-> C`. The components of this cocone are given by

```text
  i'' := i' ∘ i
  j'' := j'
  H'' := (i ·l H) ∙h (H' ·r g).
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (𝒮 : span-diagram l1 l2 l3)
  {C : UU l4} {X : UU l5} {Y : UU l6} (h : codomain-span-diagram 𝒮 → C)
  (c : cocone-span-diagram 𝒮 X)
  (d :
    cocone-span-diagram
      ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
      ( Y))
  where

  left-map-horizontal-comp-cocone-span-diagram :
    domain-span-diagram 𝒮 → Y
  left-map-horizontal-comp-cocone-span-diagram =
    left-map-cocone-span-diagram
      ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
      ( d) ∘
    left-map-cocone-span-diagram 𝒮 c

  right-map-horizontal-comp-cocone-span-diagram : C → Y
  right-map-horizontal-comp-cocone-span-diagram =
    right-map-cocone-span-diagram
      ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
      ( d)

  coherence-square-horizontal-comp-cocone-span-diagram :
    coherence-square-maps
      ( h ∘ right-map-span-diagram 𝒮)
      ( left-map-span-diagram 𝒮)
      ( right-map-horizontal-comp-cocone-span-diagram)
      ( left-map-horizontal-comp-cocone-span-diagram)
  coherence-square-horizontal-comp-cocone-span-diagram =
    pasting-horizontal-coherence-square-maps
      ( right-map-span-diagram 𝒮)
      ( h)
      ( left-map-span-diagram 𝒮)
      ( right-map-cocone-span-diagram 𝒮 c)
      ( right-map-cocone-span-diagram
        ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
        ( d))
      ( left-map-cocone-span-diagram 𝒮 c)
      ( left-map-cocone-span-diagram
        ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
        ( d))
      ( coherence-square-cocone-span-diagram 𝒮 c)
      ( coherence-square-cocone-span-diagram
        ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
        ( d))

  horizontal-comp-cocone-span-diagram :
    cocone-span-diagram (right-concat-span-diagram 𝒮 h) Y
  pr1 horizontal-comp-cocone-span-diagram =
    left-map-horizontal-comp-cocone-span-diagram
  pr1 (pr2 horizontal-comp-cocone-span-diagram) =
    right-map-horizontal-comp-cocone-span-diagram
  pr2 (pr2 horizontal-comp-cocone-span-diagram) =
    coherence-square-horizontal-comp-cocone-span-diagram
```

### Concatenation of cocones under span diagrams and morphisms and equivalences of arrows on the left

Consider a span diagram `s := A <-f- S -g-> B`, a cocone on `𝒮`, and a
[moprhism of arrows](foundation.morphisms-arrows.md) `h : hom-arrow f' f` for
some map `f : S' → A'`, as indicated in the diagram

```text
          h₀       g
     S' -----> S -----> B
     |         |        |
  f' |    h    | f      | j
     v         v        v
     A' -----> A -----> X
          h₁       i
```

Then we obtain a new cocone `(i' , j' , H')` on the outer span diagram
`A' <- S' -> B`. The components of this new cocone are:

```text
  i' := i ∘ h₁
  j' := j
  H' := (i ·l h) ∙h (H ·r h₀).
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (𝒮 : span-diagram l1 l2 l3)
  {S' : UU l4} {A' : UU l5} (f' : S' → A') {X : UU l6}
  where

  cocone-left-concat-hom-arrow-span-diagram :
    (h : hom-arrow f' (left-map-span-diagram 𝒮)) → cocone-span-diagram 𝒮 X →
    cocone-span-diagram (left-concat-hom-arrow-span-diagram 𝒮 f' h) X
  cocone-left-concat-hom-arrow-span-diagram h c =
    horizontal-comp-cocone-span-diagram
      ( span-diagram-hom-arrow f' (left-map-span-diagram 𝒮) h)
      ( right-map-span-diagram 𝒮)
      ( cocone-hom-arrow f' (left-map-span-diagram 𝒮) h)
      ( c)

  cocone-left-concat-equiv-arrow-span-diagram :
    (e : equiv-arrow f' (left-map-span-diagram 𝒮)) → cocone-span-diagram 𝒮 X →
    cocone-span-diagram (left-concat-equiv-arrow-span-diagram 𝒮 f' e) X
  cocone-left-concat-equiv-arrow-span-diagram e =
    cocone-left-concat-hom-arrow-span-diagram
      ( hom-equiv-arrow f' (left-map-span-diagram 𝒮) e)
```

Consider a span diagram `𝒮 := A <-f- S -g-> B`, a cocone `(i , j , H)` on `𝒮`,
and a moprhism of arrows `h : hom-arrow j j'` for some map `j' : B' → X'`, as
indicated in the diagram

```text
        g        h₀
    S -----> B -----> B'
    |        |        |
  f |      j |   h    | j'
    v        v        ∨
    A -----> X -----> X'
        i        h₁
```

Then we obtain a new cocone on the outer span diagram `A <- S -> B'`.

### Vertical composition of cocones under span diagrams

Consider a span diagram `𝒮 := A <-f- S -g-> B` and a map `h : A → C`. Then we
can **compose** a cocone `c := (i , j , H)` under `𝒮` **on the right** with a
cocone `d` under the span diagram `C <-h- A -i-> X` as indicated in the diagram

```text
        g
    S -----> B
    |        |
  f |        | j
    v   i    v
    A -----> X
    |        |
  h |        | j'
    v        v
    C -----> Y
        i'
```

to obtain a cocone `(i'' , j'' , H'')` under the span diagram
`C <-h∘f- S -g-> B`. The components of this new cocone are given by

```text
  i'' := i'
  j'' := j' ∘ j
  H'' := (H' ·r f) ∙h (j' ·l H).
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (𝒮 : span-diagram l1 l2 l3)
  {C : UU l4} (h : domain-span-diagram 𝒮 → C) {X : UU l5} {Y : UU l6}
  (c : cocone-span-diagram 𝒮 X)
  (d :
    cocone-span-diagram
      ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
      ( Y))
  where

  left-map-vertical-comp-cocone-span-diagram : C → Y
  left-map-vertical-comp-cocone-span-diagram =
    left-map-cocone-span-diagram
      ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
      ( d)

  right-map-vertical-comp-cocone-span-diagram : codomain-span-diagram 𝒮 → Y
  right-map-vertical-comp-cocone-span-diagram =
    right-map-cocone-span-diagram
      ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
      ( d) ∘
    right-map-cocone-span-diagram 𝒮 c

  coherence-square-vertical-comp-cocone-span-diagram :
    coherence-square-maps
      ( right-map-span-diagram 𝒮)
      ( h ∘ left-map-span-diagram 𝒮)
      ( right-map-vertical-comp-cocone-span-diagram)
      ( left-map-vertical-comp-cocone-span-diagram)
  coherence-square-vertical-comp-cocone-span-diagram =
    pasting-vertical-coherence-square-maps
      ( right-map-span-diagram 𝒮)
      ( left-map-span-diagram 𝒮)
      ( right-map-cocone-span-diagram 𝒮 c)
      ( left-map-cocone-span-diagram 𝒮 c)
      ( h)
      ( right-map-cocone-span-diagram
        ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
        ( d))
      ( left-map-cocone-span-diagram
        ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
        ( d))
      ( coherence-square-cocone-span-diagram 𝒮 c)
      ( coherence-square-cocone-span-diagram
        ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
        ( d))

  vertical-comp-cocone-span-diagram :
    cocone-span-diagram (left-concat-span-diagram 𝒮 h) Y
  pr1 vertical-comp-cocone-span-diagram =
    left-map-vertical-comp-cocone-span-diagram
  pr1 (pr2 vertical-comp-cocone-span-diagram) =
    right-map-vertical-comp-cocone-span-diagram
  pr2 (pr2 vertical-comp-cocone-span-diagram) =
    coherence-square-vertical-comp-cocone-span-diagram
```

### Composing cocones with morphisms of arrows on the right

Consider a span diagram `s := A <-f- S -g-> B` and a map `g' : S' → B'`. Then we
can **compose** a morphism of arrows `h : hom-arrow g' g` with a cocone
`c := (i , j , H)` under `𝒮`, as indicated in the diagram

```text
         g'
     S' ----> B'
     |        |
  h₀ |   h    | h₁
     v   g    v
     S -----> B
     |        |
   f |        | j
     v        v
     A -----> X
         i
```

to obtain a cocone `(i' , j' , H')` under the span diagram `A <- S' -> B'`. The
components of this new cocone are given by

```text
  i' := i
  j' := j ∘ h₁
  H' := (H ·r h₀) ∙h (j ·l h).
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (𝒮 : span-diagram l1 l2 l3)
  {S' : UU l4} {B' : UU l5} (g' : S' → B') {X : UU l6}
  where

  cocone-right-concat-hom-arrow-span-diagram :
    (h : hom-arrow g' (right-map-span-diagram 𝒮)) → cocone-span-diagram 𝒮 X →
    cocone-span-diagram (right-concat-hom-arrow-span-diagram 𝒮 g' h) X
  cocone-right-concat-hom-arrow-span-diagram h c =
    vertical-comp-cocone-span-diagram
      ( span-diagram-hom-arrow
        ( map-domain-hom-arrow g' (right-map-span-diagram 𝒮) h)
        ( map-codomain-hom-arrow g' (right-map-span-diagram 𝒮) h)
        ( transpose-hom-arrow g' (right-map-span-diagram 𝒮) h))
      ( left-map-span-diagram 𝒮)
      ( cocone-hom-arrow
        ( map-domain-hom-arrow g' (right-map-span-diagram 𝒮) h)
        ( map-codomain-hom-arrow g' (right-map-span-diagram 𝒮) h)
        ( transpose-hom-arrow g' (right-map-span-diagram 𝒮) h))
      ( c)

  cocone-right-concat-equiv-arrow-span-diagram :
    (e : equiv-arrow g' (right-map-span-diagram 𝒮)) → cocone-span-diagram 𝒮 X →
    cocone-span-diagram (right-concat-equiv-arrow-span-diagram 𝒮 g' e) X
  cocone-right-concat-equiv-arrow-span-diagram e =
    cocone-right-concat-hom-arrow-span-diagram
      ( hom-equiv-arrow g' (right-map-span-diagram 𝒮) e)
```

### Composition of cocones and morphisms of span diagrams

Consider a morphism `h := (h₀ , h₁ , h₂ , h₃ , h₄) : 𝒮 → 𝒯` of span diagrams

```text
          f'        g'
     A' <----- S' -----> B'
     |         |         |
  h₀ |      h₂ |         | h₁
     V         V         V
     A <------ S ------> B
          f         g
```

and a cocone `c := (i , j , H)` under the span `𝒮 := A <- S -> B`, as indicated
in the diagram

```text
          g'
     S' ------> B'
     | \         \
     |  \ k       \ j
     v   v     g   v
     A'   S ------> B
      \   |         |
     i \  | f       |
        v v         v
          A ------> X.
```

Then we obtain a cocone `c ∘ h` under the span `𝒮' := A' <- S' -> B'`. This
cocone is defined by first composing `c` horizontally with the morphism of
arrows `f' ⇒ f`, and then composing vertically with the morphism of arrows
`id ⇒ ?`, as indicated in the following diagram

```text
               g'
     S' --------------> B'
     |                  |
     |         h₄       | h₁
     V    h₂       g    V
     S' -----> S -----> B
     |         |        |
  f' |   h₃  f |   H    | j
     V         V        V
     A' -----> A -----> X
          h₀       i
```

The components of the resulting cocone `(i' , j' , H')` are as follows:

```text
  i' := i ∘ h₀
  j' := j ∘ h₁
  H' := ((i ·l h₃) ∙h (H ·r h₂)) ∙h (j ·l h₄)
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  (𝒮' : span-diagram l1 l2 l3) (𝒮 : span-diagram l4 l5 l6)
  (h : hom-span-diagram 𝒮' 𝒮)
  {X : UU l7} (c : cocone-span-diagram 𝒮 X)
  where

  comp-cocone-hom-span-diagram : cocone-span-diagram 𝒮' X
  comp-cocone-hom-span-diagram =
    cocone-right-concat-hom-arrow-span-diagram
      ( left-concat-hom-arrow-span-diagram 𝒮
        ( left-map-span-diagram 𝒮')
        ( left-hom-arrow-hom-span-diagram 𝒮' 𝒮 h))
      ( right-map-span-diagram 𝒮')
      ( ( id) ,
        ( map-codomain-hom-span-diagram 𝒮' 𝒮 h) ,
        ( right-square-hom-span-diagram 𝒮' 𝒮 h))
      ( cocone-left-concat-hom-arrow-span-diagram
        ( 𝒮)
        ( left-map-span-diagram 𝒮')
        ( left-hom-arrow-hom-span-diagram 𝒮' 𝒮 h)
        ( c))

module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  (𝒮' : span-diagram l1 l2 l3) (𝒮 : span-diagram l4 l5 l6)
  (e : equiv-span-diagram 𝒮' 𝒮)
  {X : UU l7} (c : cocone-span-diagram 𝒮 X)
  where

  comp-cocone-equiv-span-diagram : cocone-span-diagram 𝒮' X
  comp-cocone-equiv-span-diagram =
    comp-cocone-hom-span-diagram 𝒮' 𝒮 (hom-equiv-span-diagram 𝒮' 𝒮 e) c
```