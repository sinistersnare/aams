# Abstract Machines ... Abstracted! #

Hi these are supposed to be implementations of AM's from the AAM paper.

http://matt.might.net/papers/vanhorn2010abstract.pdf

Here are the (some?) of the machines to implement. Most of them I haven't implemented yet.

`CEK` is the simplest here (Control, Environment, Kontinuation),
`CESK` adds a store, to remove recursion in the Environment
`CESK*` now allocates the continuations in the Store.
`CESKt*` adds a time-stamp to `CESK*`, to abstract GC use.
`aCESKt*` abstracted `CESKt*`, for use in static analysis.

## License ##

MIT license! Enjoy!
