
# Mini intro : Gospel expliqué depuis la Logique de séparation

## Partons d'une spec CFML

``` 
forall x y,
  P ->
  SPEC (f x)
  PRE H
  POST (fun r => exists z, [P'] * H')
```

où y et z dénotent des valeurs ghosts/auxiliaires/logiques en entrée et sortie, 
et les crochets des parties pures. 


## Etape 1 : passer en syntaxe requires/ensures

Les crochets dénotent maintenant les variables ghost.

``` 
GOSPEL:  r,[z] = f x [y]
consumes H
requires P
produces H'
ensures P'
```

## Etape 2 : normaliser la forme des prédicats de représentation

Prenons un morceau de H ou de H'. Il est de la forme :
``` 
  p ~> R X Y Z
```

S'il y a plusieurs arguments à R (plusieurs champs modèles),
on se ramène à une seul argument via un record :
``` 
  p ~> R X
```

Et si c'est une région groupe, "GroupOf R M",
on lui ajoute un nom pour pouvoir le tenir:
``` 
  r ~> (GroupOf R) M
```

## Etape 3 : réduire le nombre de variables auxiliaires


Tous les prédicats de représentation sont maintenant de la forme :

``` 
  x ~> R X
```

Afin de réduire le nombre de variables, on remplace la notation `~>` par la notation `@`,
en ne bindant qu'un seul nom. Ainsi, on remplace :

``` 
  consumes x ~> R X
```

par

``` 
  consumes x @ R
```

et dans la clause requires, une occurence de `x` fait référence au modèle `X`.

On propose la syntaxe `&x` pour faire référence à la valeur Caml qui s'appelait `x` en CFML, en général une adresse. Il faut voir `&` comme un opérateur méta et pas comme une fonction. C'est très similaire à ce qu'il y a dans le langage C (et d'autres), où on a les opérateurs méta `&x` et `type of x`. Noter que `old x` est également une opération méta, qui existe déjà dans Gospel.

De même on remplace :

``` 
  produces x ~> R Y
```

par

``` 
  produces x @ R
```

et dans la clause `ensures`, on écrit `x` pour signifier le nouveau modèle `Y`,
et `old x` pour faire référence au modèle `X` introduit par la clause `consumes`. 



## Etape 4 : nommer les prédicats de représentation via des expressions de types spaciaux

En syntaxe CFML:

``` 
  produces x ~> (RefOf Int) X
```

devient en Gospel

``` 
  produces x @ int ref
```
où `int ref` est un type spatial, exprimé dans une syntaxe très proche de la syntaxe des types OCaml.

L'originalité principale des types spaciaux est la possibilité de couper la référence, par exemple `int ref array` vs `any array` (a.k.a. prédicat `Id` en CFML). 

Question : quand est-ce qu'un `foo list` est duplicable ? Par exemple `int ref list` traduit de la possession, non duplicable. En revanche, `loc list` et `int list` sont duplicables.

Idée (François) : `int` pourrait être un prédicat de représentation pour un entier machine de type `int` modélisé comme un entier idéal de type `integer`. Par exemple, si on écrit:

``` 
  f (x : int)
    preserves x @ int (* on peut omettre cette ligne, c'est le défaut *)
```
alors dans les clauses `requires` et `ensures`, la variable `x` serait un entier idéal de type `integer`, tandis que `&x` serait une valeur OCaml de type `int`. Le prédicat de représentation impliquerait la propriété `min_int <= x <= max_int`.


## Etape 5 : sucre pour réduire les consumes/produces


(1) On introduit le sucre :

```
  modifies x @ t
```

pour :

```
   consumes   x @ t
   produces   x @ t
```

et idem on a le sucre :

```
  modifies x
```

pour :

```
   consumes   x
   produces   x
```

(2) On introduit le sucre :

```
  preserves x @ t    (alternative: maintains x@t, ou reads x@t)
``` 

ou juste

```
  preserves x
```

pour une permission lecture seule. Pour l'instant, on ne spécifie pas comment sont représentées les permissions (duplicables) en lecture seule, mais on pourrait imaginer que ça se traduise par des fractions.

```
   (avec un argument ghost supplémentaire a)
   consumes   x^a
   produces   x^a
   ensures    old x = x   (ligne probablement optionnel)
```

## Etape 6 : clauses preserves et produces par défaut 

On décrête que pour chaque argument `x` du prototype de la fonction, si `x` n'est pas mentionné dans une clause `consumes` ou `modifies`, alors on ajoute automatiquement la ligne :

```
   preserves x
```

Motivation : `preserves` est un bon défaut. Ça ne servirait à rien d'avoir un argument de fonction qu'on ne peut pas utiliser. Et ça ne serait pas une bonne idée d'avoir un `modifies` par défaut.

On décrête que chaque valeur de retour `y` du prototype de la fonction, on a automatiquement une clause `produces y`.

## Résumé des combinaisons utiles 

Pour un argument `x`, on peut avoir 3 types de spécification.

(1) Permission en lecture seule:
- aucune clause parmi `consumes/produces/produces/preserves x`: c'est implicitement `preserves x`, avec le prédicat de représentation par défaut: la fonction prend l'argument en lecture seule, et rend la permission à la fin. La clause `requires` fait référence à `x`. La clause `ensures` fait également référence à `x`. L'expression `old x` est soit définie comme étant un synonyme de `x`, soit interdite syntaxiquement (à définir).
- `preserves x @ t` : comme le cas précédent, `x` est en lecture seul, simplement avec un prédicat de représentation qui n'est pas forcément celui par défaut

(2) Permission en écriture:
- `modifies x` (ou `modifies x @ t` ): la fonction prend l'argument en lecture-écriture et rend cette permission. La clause `requires` fait référence `x`. La clause `ensures` fait référence à `old x` et à `x`.
- `consumes x @ t` et `produces x @ u`  en même temps: c'est une version généralisée du `modifies x`, où la fonction l'argument et le rend ensuite avec un autre prédicat de représentation. En général, `old x` et `x` n'ont dans ce cas pas le même type.

(3) Permission en écriture non rendue:
- `consumes x` (ou `consumes x @ t`) sans `produces x`: la fonction prend la possession de l'argument et ne la rend pas. La clause `requires` peut utiliser `x`. La clause `ensures` fait référence à `old x` mais ne peut pas faire référence à `x`.

Pour une valeur de retour `y`, on peut avoir des champs `produces y` ou `produces y @ t`. La clause `ensures` fait référence à `y`. La syntaxe `old y` est invalide. Si la valeur de retour `y` a un type duplicable, le `produces y ` est implicite.

[Plus tard] Pour renvoyer des permissions en lecture seule, il faudra utiliser des permissions fractionnaires.

[Plus tard] y a t-il des exemples où on voudrait avoir plusieurs `x @ ...` ? (ce qui poserait problème pour savoir lequel détermine le modèle)

# Quelques exemples supplémentaires


  
## Union Find

```
(* noter que 'a node est duplicable; 
   son modèle logique est une valeur de type loc *)

(* voir les champs modèls et les invariants plus loin dans ce doc,
   issue du gospel.mli de vocal; ici, on donne l'instantiation. *)

ghost type 'a uf = (loc,'a) group
(* le group est un type spatial, représenté dans la logique au type
   (loc,'a') group *)
  r : 'a uf
  model : { dom : 'a elem set '; 
            rep : 'a elem -> 'a elem;
            img : 'a elem -> 'a }
  invariant is_uf_graph r (model r)  (* defined e.g. in Coq *)
  
 où [is_uf_graph r R] énonce, en particulier, que:
   is_reverse_forest r
   R.dom = Map.dom r
   R.img = Map.get r (* application partielle *)
   R.rep = (fonction qui suit le chemin uniques dans le graphe décrit par r)
  
  
(*@ val create: unit -> 'a uf *)
(*@ uf = create ()
      (* noter que le [produces r] est implicite *)
      ensures uf.dom = {} *)

val make : 'a -> 'a elem
(*@ e = make [uf: 'a uf] v
      (* noter le consumes v implicite *)
      modifies uf
      ensures  not (mem e (old uf.dom))
      ensures  uf = UF.add (old uf) e v *)
      
(* Noter que c'est la définition logique [UF.add R e v] qui définit 
   l'évolution du modèle:
      { dom = Set.add e R.dom;
        rep = R.rep[e -> e];
        img = R.img[e -> v] }
   même s'il reste possible d'inliner ces égalités, si on veut.
   l'avantage de nommer l'opération, est qu'on peut plus facilement
   énoncer des lemmes sur [UF.add]. *)

val repr : 'a node -> 'a node 
  (*@ y = repr [uf : 'a uf] x 
        modifies r
        requires mem x uf.dom 
        ensures y = repr uf x 
  *)
  
val eq : 'a node -> 'a node -> bool
  (*@ b = eq [uf : 'a uf] x y 
        modifies uf
        requires mem x uf.dom /\ mem y uf.dom 
        ensures old r = r /\ repr r x = repr r y
  *)
  
val union : 'a node -> 'a node -> unit
  (*@ union [r : 'a uf] x y 
        modifies uf
        requires mem x uf.dom /\ mem y uf.dom 
        ensures ...
  *)
  
val get : 'a node -> 'a  (* cas simple, valeurs duplicable *)
  (*@ v = get x [r : 'a uf]
        duplicable 'a
        modifies r
        requires mem x uf.dom 
        ensures old r = r /\ v = img r
  *)
``` 

   
   
## Remarques sur la spec actuelle de Gospel UF
```
(*@ type 'a uf *)
(*@ mutable model dom : 'a elem set
    mutable model rep : 'a elem -> 'a elem
    mutable model img : 'a elem -> 'a
    invariant forall x: 'a elem. mem x dom -> img x = img (rep x)
    invariant forall x: 'a elem. mem x dom -> rep (rep x) = rep x
    invariant forall x: 'a elem. mem x dom -> mem (rep x) dom *)

(*@ predicate equiv (uf: 'a uf) (x: 'a elem) (y: 'a elem) =
      uf.rep x = uf.rep y *)

(*@ val create: unit -> 'a uf *)
(*@ uf = create ()
      ensures uf.dom = {} *)
```

Est-ce qu'on a un exemple montrant comment instantier uf ?
(voir une proposition plus haut dans le doc).

Est ce qu'on peut accepter aussi la syntaxe record pour le model?
```
(*@ type 'a uf *)
(*@ model : { 
    mutable dom : 'a elem set;
    mutable rep : 'a elem -> 'a elem;
    mutable img : 'a elem -> 'a; } *)
```

Est-ce qu'on peut factoriser les champs inchanger, du coup? Cad que:
```
      ensures  uf.dom = old uf.dom
      ensures  uf.rep = old uf.rep
      ensures  uf.img = old uf.img
```   
deviendrait simplement
```
      ensures  uf = old uf
```   
      
Est-ce qu'on pourrait nommer les invariants, afin de pouvoir
y faire référence dans des outils de preuve? 

```
    invariant img_rep : forall x: 'a elem. mem x dom -> img x = img (rep x)
    invariant rep_rep : forall x: 'a elem. mem x dom -> rep (rep x) = rep x
    invariant dom_rep : forall x: 'a elem. mem x dom -> mem (rep x) dom *)
```
Est-ce qu'un record d'invariants serait équivalent?

```
    invariant {
      img_rep : forall x: 'a elem. mem x dom -> img x = img (rep x);
      rep_rep : forall x: 'a elem. mem x dom -> rep (rep x) = rep x;
      dom_rep : forall x: 'a elem. mem x dom -> mem (rep x) dom; } *)
```

## Magic wand: exemple sur le get de Union Find avec éléments non duplicables

Le type `entailment` est un alias pour le type `unit->unit`
des fonctions ghosts pouvant être utilisées autant de fois qu'on veut. Une fonction est représentée (modélisée) dans la logique par un token sur lequel on peut énoncer des spécifications (comme en CFML). Ci-dessous, j'utilise le mot clé `spec pour introduire une spec d'une fonction local (on aura besoin de ce mot clé pour la plupart des fonctions qui prennent en argument ou bien qui retourne des fonctions).
 
Le type `wand` est un alias pour le type `entailment` vu comme un type linéaire, c'est-à-dire d'une fonction ghost pouvant être utilisée une seule fois.

```  
val get : 'a node -> 'a  (* cas d'une lecture en read-only *)
  (*@ [close : wand], v = get [r : 'a uf] [k : frac] x
        consumes r^k
        produces v^k
        (* implicitement, on a [produces close_hole], qui donne
           la permission a appeler une fois la fonction [close_hole] *)
        (* description ci-dessous de (v^k --* r^k) *)
        ensures (spec close () 
              consumes v^k
              produces r^k)
        requires mem x uf.dom 
        ensures old r = r /\ v = img r
        (* noter: pas clair qu'on puisse laisser [old r = r] implicite *)
  *)
```

On pourrait encoder `wand` comme une fonction `f` de type `entailment` qui a un `consumes f_call`, où `f_call` est une permission fournie abstraite en un exemplaire avec la fonction au moment où est elle introduite. Mais on va cacher ça à l'utilisateur, sinon ça fera trop de bruit. Si on voulait le faire explicitement, on aurait, avec `p` la permission abstraite, typée au type spécial `hprop`.

```  
val get : 'a node -> 'a  (* variante explicite de la spec ci-dessus *)
  (*@ [p : hprop], [close : entailment], v = get [r : 'a uf] [k : frac] x
        consumes r^k
        produces v^k  (* implicitement, on a [produces p] *)
        ensures (spec close () 
              consumes p, v^k  (* ici on consomme p *)
              produces r^k)
        requires mem x uf.dom 
        ensures old r = r /\ v = img r
        (* noter: pas clair qu'on puisse laisser [old r = r] implicite *)
  *)
```


## Stack possédant ses éléments

`duplicable 'a` signifie que pour `x : 'a`  un `consumes x` ou un `produces x` est toujours gratuitement satisfiable.


Spec de push et pop fonctionnent sur des types 'a non duplicables,
   et a fortiori sur des types duplicables 

```
val push : 'a stack -> 'a -> unit
  (*@ push s x
        modifies s
        consumes x
        ensures s = x :: old s
  *)
  
  val pop : 'a stack -> 'a
  (*@ x = pop s
        modifies s
        produces x
        requires s <> []
        ensures old s = x :: s
  *)
```

Spec de top pour éléments duplicables.

```
  val top : 'a stack -> 'a  (* cas éléments duplicables *)
  (*@ x = top s
        duplicable 'a
        requires s <> []
        ensures x = Seq.head s
  *)
```


Spec de top pour éléments non duplicables, en read-write.


```
(* top en read-write, bloquant la pile *)
  val top : 'a stack -> 'a 
  (*@ [close:wand], x = top s 
        consumes s as s_old (* je bind un nom pour le wand *)
        produces x
        produces (spec close ()    
            consumes x (* le model a pu changer *)
            produces s
            ensures s = y :: Seq.tail s_old) 
        requires s <> []
        ensures x = Seq.head s
  *)  
  
(* spec dérivée de pop, pour jeter un élément
   de tête après un top qui a déjà extrait l'élément *)
  val pop : 'a stack -> 'a 
  (*@ y = pop [close:wand] [x:'a] s
        consumes (spec close () consumes x produces s
                  ensures s = y :: Seq.tail s_old)
        modifies s
        produces y@any
        requires x = Seq.head s
        ensures s = Seq.tail (old s)
        ensures &y = &x      (* équivalent à [y = &x] *)
  *)
```

Spec de top pour éléments non duplicables, en read-only (avec une fraction).

```
  val top : 'a stack -> 'a 
  (*@ [close : wand], x = top [k : frac] s
        consumes s^k  
        produces x^k 
        ensures (spec close () consumes x^k produces s^k)
        requires s <> []
        ensures x = Seq.head s *)
```

------------
Détails Armaël

# Exemple introductif

Dans le système proposé ci-dessous, la spécification pour une fonction `incrall`
incrémentant tous les entiers d'une matrice (un `int array array`) s'écrit comme
suit :

```
val incrall : int array array -> unit
(*@ incrall m
      modifies m
      ensures forall 0 <= i < length m.
        forall 0 <= j < length m[i].
          m[i][j] = old m[i][j] + 1
*)
```

Dans la clause `ensures`, `length` et `[_]` sont des opérations *logiques* sur
le modèle *logique* des tableaux, i.e. des séquences pures. Dans la clause
`ensures`, `m` désigne donc une séquence de séquence d'entiers. 
Écrite ainsi, la spécification correspond ici au cas où on a la possession
récursive sur la matrice, ce qui veut dire qu'il ne peut pas avoir d'aliasing
entre les sous-tableaux.

La spécification ci-dessus est vue comme du sucre syntaxique pour la
spécification désucrée suivante (que l'on peut écrire aussi à la main si on on
veut), et qui explicite les questions de possession grâce à deux clauses
`consumes` et `produces`, qui spécifient des assertions dans un langage
d'*assertions spatiales*.

```
val incrall : int array array -> unit
(*@ incrall m
      consumes m @ int array array
      produces m @ int array array
      ensures forall 0 <= i < length m.
        forall 0 <= j < length m[i].
          m[i][j] = old m[i][j] + 1
*)
```


# Rappel : prédicats de représentation d'ordre supérieur en logique de séparation

On veut que nos specs se désucrent en des assertions de logique de séparation
utilisant des prédicats de représentation, potentiellement d'ordre supérieur
(type paramétré en ocaml => prédicat de représentation paramétré par un prédicat
de représentation).

La forme générale du type d'un prédicat de représentation est la suivante :
```
R : model -> impl -> Hprop
```

où `model` est le type du modèle logique, et `impl` le type des valeurs de programmes.

## Quels sont les types des "valeurs de programmes" ? 

On se place dans le même cadre que CFML : les types de données purs (int, list, etc) sont représentés par un type logique équivalent, et les types de données mutables (ref, array, etc) sont représentés par le type `loc` des locations.

Exemples: type ocaml  ->  type logique des valeurs
- `int ref` -> `loc`
- `int list` -> `list int`
- `int list ref` -> `loc`
- `int ref list` -> `list loc`
- `int ref ref list` -> `list loc`

Le type des valeurs de programme est toujours(?) dérivable depuis le type OCaml des valeurs.
Le type des modèles peut lui être ce que l'on veut, et est seulememt déterminé par le prédicat de représentation.

## Prédicats de représentation d'ordre supérieur

À chaque type de conteneur, autant pur que mutable, on associe un prédicat de
représentation d'ordre supérieur, paramétré par le prédicat de représentation
sur les éléments.

Exemples :

- références
```
(* modèle logique d'une référence *)
Inductive box A := { contents : A }.

RefOf : ∀ {A a}, (A -> a -> Hprop) -> box A -> loc -> Hprop
```

-> si les éléments de la référence sont représentés par un prédicat `R`, reliant
un modèle logique de type `A` à des valeurs de type `a`, alors `RefOf R` relie
un modèle logique de type `box A` à des valeurs de type `loc`.

- listes immutables
```
ListOf : ∀ {A a}, (A -> a -> Hprop) -> list A -> list a -> Hprop
```

- valeurs pures ground / valeurs sans possession
```
Id : ∀ A, (A -> A -> Hprop)
```

**À noter**: `Id` n'est pas un prédicat de représentation ! C'est une famille
de prédicats de représentation, paramétrée par le type `A`. Étant donné une
valeur de programme, on peut regarder son type OCaml, en déduire son type en
tant que "valeur de programme", et instantiier `Id` en conséquence.
Mais `Id` en isolation n'a pas de sens en tant que prédicat de représentation.

- et en combinant les prédicats ci-dessus :

```
(* int ref list ref *)
RefOf (ListOf (RefOf (Id int))) : box (list (box int)) -> loc -> Hprop

(* int ref list *)
ListOf (RefOf (Id int)) : list (box int) -> list loc -> Hprop

(* int list ref *)
RefOf (ListOf (Id int)) : box (list int) -> loc -> Hprop
```

## Pour la suite

On en retient qu'un prédicat de représentation détermine *deux* types logiques :
le type `model` et le type `impl`.

Ces deux types sont les mêmes lorsque l'on utilise le "prédicat de
représentation" `Id`, à condition de savoir l'instancier (par exemple en sachant
le type OCaml de la valeur concernée).

## Pour plus tard

Le modèle des types de valeurs de programme est probablement à raffiner en
présence de records et surtout de déclarations de type du genre :

```
type 'a mlist = Nil | Cons of { head : 'a; mutable tail : 'a mlist }
```

# Proposition

## Types spatiaux et assertions spatiales

- on introduit un namespace séparé de *types spatiaux* (qui suivent la même grammaire que les types OCaml)
  + les types spatiaux correspondent à des prédicats de représentation
  + pour chaque type ocaml, on a un type spatial du même nom
  + par ailleurs, on a un type spatial supplémentaire *spécial* appelé `any`;
    il correspond au prédicat de représentation `Id`, et ne sera autorisé que dans
    des contextes où on sait comment l'instancier

- on introduit des nouvelles *clauses spatiales* permettant de spécifier des
  informations de possession en utilisant les types spatiaux. Les nouvelles
  clauses sont `modifies`, `preserves`, `consumes` et `produces`.

- chaque clause prend en argument une liste d'*assertions spatiales* séparées
  par des virgules, de la forme `x @ t`, où :
  + `x` est le nom d'un argument ou valeur de retour
  + `t` est un type spatial

- l'assertion `x @ t` désigne la possession de `x` telle que décrite par le type
  spatial `t`
- une assertion `x @ u` n'est bien typée que si le type OCaml de `x` est
  compatible avec `u` (pour la relation de compat définie comme on l'imagine..)

- le désucrage / traduction des clauses spatiales se fait séparément pour chaque
  argument / valeur de retour, comme suit :
  + on peut écrire `x` à la place de `x @ t`, où `t` est le lifting en type
    spatial du type OCaml `t` de `x`
  + `modifies x @ t` est du sucre pour `consumes x @ t` + `produces x @ t`
  + `preserves x @ t` se désucre en `consumes`+`produces` avec une permission
    lecture seule (notion à déterminer). En première approche, une alternative
    plus limitée mais correcte serait de le désucrer en `consumes x @ t` +
    `produces x @ t` + le modèle logique reste le même.
  + pour chaque argument, si `x` n'est pas mentionné dans `consumes` ou
    `produces`, on ajoute `preserves x`
  + pour chaque valeur de retour, si `x` n'est pas mentionné dans une clause
    `produces`, on ajoute automatiquement `produces y`.


## Types spatiaux : modèle logique & types des valeurs

- à chaque type OCaml on associe un type spatial par défaut (donc un prédicat de
  représentation), associé à deux types logiques : le type du modèle, et le type
  des valeurs de programme. Autrement dit, pour chaque type OCaml, il nous faut
  déterminer quel est le type logique du modèle, **et** quel est le type logique
  des valeurs.

- pour les types OCaml purs, le modèle et les valeurs ont le même type logique,
  qui est le reflet du type OCaml. On donne au type logique le même nom que le
  type OCaml (mais dans le namespace des types logiques, donc).

- pour les types OCaml builtin mutables (ref, array, ..), on a besoin de deux
  types. Un des deux pourra être nommé comme le type OCaml.
  + choix 1: on nomme le type des valeurs comme le type OCaml. Dans ce cas,
    `int array`,`int ref` correspondent dans la logique à des types d'addresses,
    et on a des types de noms différents pour le modèle (`int seq`, `int box`?)
  + choix 2: on nomme le type des modèles comme le type OCaml. Dans ce cas,
    `int array` est un alias dans la logique pour des séquences logiques.
    On a alors un type `loc` pour les valeurs.

- pour les types abstraits, c'est un peu plus compliqué
  + si ils sont duplicables, alors on a besoin que d'un seul type logique pour
    le modèle et les valeurs
  + mais pour un type abstrait ephemeral sans annotation de modèle
    (`type t (*@ ephemeral *)`), on a besoin de deux types abstraits dans la
    logique. Quel noms utiliser ? On aimerait qu'ils soient dérivés de manière
    systèmatique depuis le nom `t`, sans clasher avec d'autres types existant.
    Idée: `&t` pour le type logique des valeurs, et `t` pour le type des modèles ?
    Ou alors, `t` pour le type des valeurs, et `^t` pour le type des modèles ?
  + *NB*: on ne peut pas choisir `loc` comme type des valeurs pour un type abstrait
    ephemere, car les valeurs sous-jacentes pourraient être des `int ref list` (en 
    ocaml), donc de type valeur `loc list` et non `loc`...
  + pour un type abstrait ephemere avec un ou plusieurs champs modèle, on génère
    un type record logique avec autant de champs que de champs modèle. (restent
    les mêmes problèmes de nommage)
  + proposition de nouvelle syntaxe : si on écrit `model: foo`, alors le modèle
    du type abstrait est directement `foo` (sans record et champ intermédiaire)

- pour les variables de types (dans les fonctions polymorphes): même problématique
  que pour les types abstraits.

## Liaison de noms entre clauses consumes/produces et clauses requires/ensures

- une assertion spatiale `x @ t`:
  + demande que `x` soit le nom d'un des paramètres ou valeurs de retour
  + bind le nom `x` au **modèle** de ce paramètre/valeur de retour dans les clauses 
    `requires`/`ensures`
  + plus précisément, `x @ t` dans une clause `consumes` bind `x` pour les clauses
    `requires`, et dans une clause `produces` il bind `x` pour les clauses `ensures`.

- conséquence : dans une clause `requires`/`ensures`, `x` n'a pas "le" type de `x`,
  mais le type de son modèle, tel que spécifié par l'assertion spatiale.

- dans une clause `ensures`, `old x` bind `x` au modèle de `x` **dans la
  précondition**.

## Accéder à l'addresse de valeurs possédées

- comment parler de l'addresse d'une structure mutable tout en la possédant ?
  + si on écrit `x @ int ref` alors `x` dénote son contenu (dans les clauses
    `requires`/`ensures`)
  + si on écrit `x @ any` alors `x` dénote l'addresse, mais on n'a plus la 
    possession
 
- proposition : dans les clauses `requires`/`ensures`, on peut écrire `&x`
  qui se désucre en l'addresse (NB: `&` n'est pas une fonction de la logique, son
  statut est similaire à `old`, ou `&`, `typeof` en C...).

## Polymorphisme

- contraintes : comment interpréter `'a array` en terme de possession ?
  + si on considère qu'il s'agit de possession récursive sur les éléments, alors
    on ne sait pas donner de spec simple à `Array.get` (et on ne sait pas vraiment
    quelle est la meilleure spec "compliquée" que l'on aimerait donner : structure
    à trou, ou borrowing, ou ...)
  + on aimerait qu'après désucrage, la spec "naturelle" que l'on écrit pour `Array.get`
    si on ne réfléchit pas aux questions de possession soit correcte et s'applique
    directement pour les cas simples sans aliasing/structures mutables imbriquées

Proposition :

- lorsque qu'un type OCaml paramétré apparait dans le type de la fonction que l'on
  spécifie, chaque variable de type `'a` donne lieu à une variable de type spatial
  `'a`, qui est *supposée duplicable*
- si l'on veut écrire une spec qui fonctionne aussi pour des `'a` ephemeral, on
  introduit une clause supplémentaire `affine 'a`

- c'est intéressant de noter que c'est similaire au traitement des types abstraits,
  par ex en paramètre de foncteur
  (sans annotation: `type t` , alors `t` duplicable; `type t (*@ ephemeral *)`, alors
  `t` ephemeral)

- on peut donc toujours écrire sans souci des types spatiaux avec possession récursive
  (par `int ref array`)
- mais les spécifications de fonctions polymorphes ne sont applicables directement 
  que pour des conteneurs contenant des types duplicables

- NB: on ne perd pas tant en généralité : avec un peu plus d'effort de preuve de
  la part du client (cf les exemples sur la possession de groupe plus bas), on 
  *peut* utiliser une spec polymorphe sur e.g. un `int ref array`, en le voyant 
  comme un `any array` + possession de groupe séparée pour les références du tableau


- question: quid de l'approche alternative consistant à remplacer `'a` par `any` dans
  le lifting spatial par défaut d'un type polymorphe ?

## Possession de groupe

Dans des cas d'utilisation avancée (notamment en présence d'aliasing), on a besoin
de parler de la possession d'un *groupe* de valeurs du même type (i.e. ça correspond
à une `*` itérée).

On peut l'exprimer sans étendre le langage des assertions gospel. Il suffirait
de disposer de l'interface suivante (`ghost type`, `ghost val` n'existent pas
actuellement, à discuter) :

```
ghost type 'a group
(*@ model (&'a, 'a) map *)

ghost val add : 'a group -> 'a -> unit
(*@ add g x
      affine 'a
      consumes x
      requires &x ∉ (dom g)
      ensures g = map_add (old g) &x x *)

ghost val remove : 'a group -> &'a -> 'a
(*@ remove g x
      affine 'a
      requires &x ∈ dom g
      ensures g = map_remove (old g) &x *)
```

- dans les spécifications, on a seulement besoin de pouvoir utiliser le type `'a
  ghost` (et type spatial correspondant) pour parler de la permission sur un
  groupe de `'a`.
  
- dans les preuves, on utiliserait les "fonctions ghost" `add` et `remove`;
  elles correspondent à des lemmes en logique de séparation

- pour les conteneurs mutables, un "specification pattern" est de prouver un
  lemme (fonctions ghost) qui permet de séparer la possession récursive sur la
  structure et ses éléments en la possession sur la structure + une possession
  de groupe sur les éléments. (et un autre lemme pour aller dans l'autre
  direction) Cf les exemples ci-dessous.

## Definition de types, modèle, et invariants associés (internes et externes)

TODO
(chantier ci-dessous)

### types abstraits

```
type t
(*@ model foo : int seq
    model bar : float
*)

(* proposition de nouvelle syntaxe : *)
type t
(*@ model : int seq *)

(* exemple : *)
val f : t -> unit
(*@ f x
    requires length x = 42  (* x est un int seq *)
*)

(* pourrait on alors expliquer la syntaxe d'origine comme une instance de la 
   nouvelle syntaxe.
   (le type logique du record s'appelle alors t) *)
type t
(*@ model : { foo : int seq; bar : float } *)

(* et comment faire pour le model *)
type 'a ref
(*@ model : { contents : ? } *)
```



```
(* dans stack.ml *)
type t = { mutable size : int; mutable items : int array }
(*@ r : t
      model : int seq
      owns r @ { size = size; items = items },
           items @ int array
variante avec le binding implicite des noms comme dans pattern matching
      owns r @ { size; items }, items @ int array 
    
ou à plus haut niveau, avec ownership imbriqué
      owns r @ { size @ int; items @ int array }

  
     
      invariant r = List.prefix size items
        (* ici r a le type décrit dans le champ model,
           on peut accéder à &r si on veut *)
           
et vu que ces types sont les mêmes que dans le type caml, on pourrait vouloir écrire :
      r : t
      model : int seq
      owns r
      invariant (model r) = List.prefix r.size r.items
(car on aurait un conflit bizarre si on utilisait r directement)  
*)
```

```
type t = A of int | B of { foo : int array; bar : float }
(* si on dit rien, on a un reflet logique au type
        A of int | B of { foo : loc; bar : float }*
        car on n'a pas de possession
        
        
   par contre on peut dire :
   
 (logical) type u = A of int | B of { foo : int seq; bar : float }
puis
     r : t
     model : u
     owns r @ t
     
     (* faut-il écrire un  invariant (model r) = ?? *)
     
         
  )


type t = int ref array
(*
   r : t
   model : int seq
   owns r @ t
   invariant model r = Seq.map (fun x -> x.contents) r
*)
```


## Namespaces et collisions de noms

TODO


# Exemples

J'ai adopté ci-dessous l'option où :
- le nom d'un type ocaml est donné au type logique du modèle
- les valeurs de `ref`, `array`, etc sont de type logique `loc`
- (en cas de type abstrait ou variable de type, `&t` est le nom du type des
   valeurs et `t` le nom du type du modèle)

## références

on suppose, au niveau de la logique :
```
type 'a ref = { contents : 'a }  (* modèle logique d'une ref *)
function (!) r = r.contents      (* fonction logique *)
```

```
val ref: 'a -> 'a ref
  (*@ r = ref v
      ensures !r = v *)
après désucrage :
  (*@ r = ref v
      maintains v @ 'a
      produces r @ 'a ref 
      ensures !r = v *)

val (!): 'a ref -> 'a
  (*@ v = !r
      ensures !r = v *)
après désucrage :
  (*@ v = !r
      maintains r @ 'a ref
      produces v @ 'a
      ensures !r = v *)

val (:=): 'a ref -> 'a -> unit
  (*@ r := v
        modifies r
        ensures !r = v *)
après désucrage :
  (*@ r := v
        maintains r @ 'a ref * v @ 'a
        modifies r
        ensures !r = v *)

val (==): 'a ref -> 'a ref -> unit
  (*@ b = (r1 == r2)
        maintains r1 @ any * r2 @ any
        ensures b = true ↔ r1 = r2 *)
```


## tableaux

au niveau de la logique, on a :
```
type 'a array = 'a seq (* séquences logiques *)
```


```
(* Ici, on a fait le choix d'avoir implicitement "duplicable 'a"
   si pas de clause "ephemeral 'a". Avec ce choix,
   le système doit donc interdire d'instancier ces specs avec 'a = int ref.
   On pourrait à la place demander que les `duplicable 'a` soit écrits
   explicitement
   
   Il n'est peut être pas moralement satisfaisant que ne rien dire
   corresponde à une précondition ̀duplicable 'a` et que écrire
   ̀ephemeral 'a` corresponde à l'absence de cette précondition.
   
*)

val length : 'a array -> int
  (*@ n = length a
        ensures n = length a
  *)

val get : 'a array -> int -> 'a
  (*@ x = get a i
        requires 0 <= i < length a
        ensures x = a[i]  (ou a.(i) si la syntaxe marche sur les Seq.t ?)
  *)
  
val set : 'a array -> int -> 'a -> unit
  (*@ set a i x
        modifies a
        requires 0 <= i < length a
        ensures a = old a [i -> x] (?)
  *)

val make : int -> 'a -> 'a array
  (*@ a = make n x
        requires 0 <= n
        ensures a = make n x
  *)

val append : 'a array -> 'a array -> 'a array
spec dans le cas où les tableaux sont disjoints:
  (*@ a = append a1 a2
        maintains a1 @ 'a array * a2 @ 'a array
        ensures a = a1 ++ a2
  *) 
spec générale mais plus difficile à utiliser:
  (*@ a = append [g : (loc, 'a array) group] a1 a2
        maintains a1 @ any * a2 @ any * g @@ 'a array
        requires {a1,a2} ⊆ dom g
        ensures a = g[a1] ++ g[a2]
  *)
```

```
val set : 'a array -> int -> 'a -> unit
(*@ [y : 'a] = set t i x
    ephemeral 'a
    modifies t
    consumes x
    produces y 
    requires 0 <= i < length t
    ensures y = (old t)[i] /\ t = old t [i -> x] (?)
*)

val set : int ref array -> int -> int ref -> unit
(*@ [y : int ref] = set t i x
    modifies t
    consumes x
    produces y 
    requires 0 <= i < length t
    ensures y = (old t)[i] /\ t = old t [i -> x] (?)
*)
```



## Swap de deux références

```
val swap : 'a ref -> 'a ref -> unit
(*@ swap [g : (loc, 'a ref) group] r1 r2
    maintains r1 @ any * r2 @ any * g @@ 'a ref
    requires {r1,r2} ⊆ dom g
    modifies g
    ensures g[r1] = old g[r2] /\ g[r2] = old g[r1]
*)
```

## matrices

```
val incrall : int array array -> unit
(*@ incrall m
      modifies m
      ensures forall 0 <= i < length m.
        forall 0 <= j < length m.(i).    (* ou m[i] ? *)
          m.(i).(j) = old m.(i).(j) + 1
```


## `Array.swap`

```
val swap : 'a array -> int -> int -> unit
(*@ swap a i j
      requires 0 <= i < length a && 0 <= j < length a
      modifies a
      ensures a.(i) = old a.(j) /\ a.(j) = old a.(j)
      ensures forall k. 0 <= k < length a -> k <> i -> k <> j ->
                        a.(k) = old a.(k)
*)
```

après désucrage :
```
val swap : 'a array -> int -> int -> unit
(*@ swap a i j
      consumes a @ 'a array
      produces a @ 'a array
      requires 0 <= i < length a && 0 <= j < length a
      modifies a
      ensures a.(i) = old a.(j) /\ a.(j) = old a.(j)
      ensures forall k. 0 <= k < length a -> k <> i -> k <> j ->
                        a.(k) = old a.(k)
*)
```

### `int ref list`

sans aliasing

```
val iter_incr : int ref list -> unit
(*@ iter_incr l
      modifies l
      ensures forall 0 <= i < length l. !l[i] = !(old l)[i] + 1 *)
```

avec aliasing

```
val iter_incr : int ref list -> unit
(*@ iter_incr [m : (loc, int ref) group] rs
    maintains rs @ any list * m @@ int ref
    modifies m
    requires dom m = set_of_list rs
    ensures m = map (fun r v -> v + count r rs) (old m)
*)
```

## specification pattern: explode/implode functions

explode/implode functions: a specification pattern

```
(* forme générale: *)
ghost explode_t : 'a t -> unit
(*@ [g : 'a group] = explode_t x
    nonduplicable 'a (?)
    consumes x @ 'a t
    produces g @@ 'a * x @ any t
    ensures dom g = ...
*)

(* pour les tableaux *)
ghost explode_array : 'a array -> unit
(*@ [g : (&'a, 'a) group] = explode_array a
    ephemeral 'a
    consumes a @ 'a array
    produces g @@ 'a * a @ any array
    ensures dom g = elements a /\ 
      cardinal (dom g) = length a /\ (or: nodup a ?)
      ∀ 0 <= i < length a. g[a[i]] = old a[i]
*)

ghost implode_array : 'a array -> unit
(*@ implode_array [g : (&'a, 'a) group] a
      ephemeral 'a
      consumes g @@ 'a * a @ any array
      produces a @ 'a array
      requires dom g = elements a /\ 
        cardinal (dom g) = length a (or: nodup a ?)
      ensures ∀ 0 <= i < length a. a[i] = g[old a[i]]
```


## tableaux read-only

TODO

+ veut-on supporter d'avoir plusieurs prédicats de représentation pour un même type? 
  (dans ce cas, comment les nommer, et quel est celui pris par défaut par le sucre syntaxique)
+ ou est-on ok avec déclarer un alias de type `type 'a ro_array = 'a array` dans le code OCaml?
+ quelles règles de raisonnement logique ?
+ quelles règles de compat/typage entre types ocaml et types spatiaux ?


