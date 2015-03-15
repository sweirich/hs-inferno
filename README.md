A port of Francois Pottier's inferno library from OCaml to Haskell.

See the [paper](http://gallium.inria.fr/~fpottier/biblio/pottier_abstracts.html#pottier-elaboration-13) for more information.

This translation to the world's finest imperative programming language is (so
far) fairly faithful. 

An example for core ML is in the file [test/Client.hs](test/Client.hs). This
file uses the library to implement a type inferencer as described in the
paper.

A slightly different example [test/G.hs](test/G.hs) elaborates a language with optional type annotations to itself. It is called G because that is the letter after F.

The interface to the library is contained in
[SolverM.hs](Language/Inferno/SolverM.hs).  The requirements of the
object language types are fairly small:

* The most important part of this interface is that it requires the definition
  of a shallow type.  This shallow type must be an instance of the classes
  Typeable, Traversable and Foldable as well as a new one called `ZipM`.  This
  last class compares two shallow types and throws an exception if they
  differ.

* The output type of the elaborator must also be a member of the `Output` type
  class.

Observations
------------
* I tried very hard to make the most literal translation that I could from
  OCaml to Haskell. This means that the Haskell code is more
  imperative than is ideomatic.
  
  
* One place this was a bit ridiculuous was the treatment of fresh variable 
  generation.  The ML library can encapsulate a counter in a module, and
  generate fresh variables based on that "global" state. 
  
  The Haskell version avoids the easy `unsafePerformIO` solution and instead
  defines a freshness monad. That monad constraint means that the state can be
  passed around, marking where fresh variables are necessary. But that
  freshness monad comes with its own problems: it cannot be ST or IO.  As a
  result, the library is generic about what form of references it uses.
  
* Haskell's lack of functors means that I had to resort to type
  parameterization throughout the library. That means that the interface types
  of the solver are quite hideous.  Insead of 
  
        exist :: (Variable -> Co a) -> Co (t, a)
  
  I had to index unification variables by `m` the monad that stores their
  state, (and can generate fresh ones when needed) and `s` the shallow
  structure that we need for unification. As coercions are about variables,
  that type is also parameterized by those two types.
  
        exist :: forall m t a. (MonadFresh m, MonadRef m, Traversable (Src t)) =>
         (Var m (Src t) -> m (Co m t a)) -> m (Co m t (t,a))
  
  I used type families instead of functional dependencies, so at least this
  function has 3 type arguments instead of 5.

* Bugs in the example code are very hard to debug! I spent much time trying to
  track down an error in my ZipM instance.

TODO
----
  - Replace `VarMap` with a more efficient data structure. Unfortunately, the
    Haskell implementation for Hashtables is not generic over the IO / ST monad
	 so it looks like I should just commit to one or the other. That will have the
	 benefit of simplifying *many* of the types.
  
  - Break out parts such as `TRef`, `MonadEqRef`, `TUnionFind`, and
    `MonadFresh` into a separate project.

  - Replace exceptions with something else? Or figure out how to get the type
    inferencer to give better error messages at least?

(Planned) Extensions
------------------------
- type annotations (done)
- polymorphic recursion
- type classes
- GADTs
- kinds
- higher-rank polymorphism

Library Overview
----------------

SolverHi.hs

SolverLo.hs