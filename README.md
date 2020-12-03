# Abstract Machines ... Abstracted! #

I wrote about what abstraction machines are
[on my blog here](https://drs.is/post/abstract-machines/).
This repo implements an abstract machine: a `time-stamped CESK*` Machine.
I then use concepts from the
['Abstracting Abstract Machines' paper](http://matt.might.net/papers/vanhorn2010abstract.pdf)
To create a static-analysis of it.

* `latex/`: Formalizations of these machines in LaTeX computer-sciencese.
* `src/`: Implementation of the formalizations in both `Racket` and `Rust`.
* `examples/`: Example scheme programs that the machines should accept.

The formalizations of these machines are available in the `latex/` directory.

I have both Racket and Rust implementations of the machine. See `src/` for those.

In the `examples/` directory are some basic scheme programs accepted by these machines.


## Running ##

To run the Rust code

```bash
cargo run -- examples/basic.scm # to run a scheme file
cargo run # to start a REPL
```

For Racket, load the machine up in your Racket environment of choice,
and use the `evaluate` function to run a program.

```racket
> (evaluate '(prim + 3 4 (let ([x 6] [y 10]) (prim + x y))))
```

## Abstrat Interpretation ##

Abstract Interpretation is a style of static-analysis that attempts
to run the program in a decidably computable, sound way
(No we did not have to solve the halting problem).
By computing using abstract values insted of concrete values,
we can over-approximate program behavior.

'Abstracting Abstract Machines' shows how we can use Abstract Machines
to more easily create abstract interpreters. Thats what we are doing here,
We first implement a concrete machine, and then we lift it into abstract-space
to create an analysis.

## Future Work / TODO ##

I also plan on implementing Delimited Continuations instead of one-shot
continuations. DCs are much more efficient and powerful.
Hopefully after I get the analysis finished, I can start on this!

I want to extend the machines semantics to cover most of
[SinScheme](https://github.com/sinistersnare/SinScheme).
That way, I can do a static analysis of it, and perform real optimizations
on it. This is a a stretch goal, but I think its doable!

* Its probably better for the `setk` continuation to take the address outright,
instead of figuring out the address later. Thats what AAM does... And AAM == right.
	* This would mean changes in all implementations and the formalizations!
	* Done in Rust, now impl in Formalization! Then Racket!
* appprimk does not need an env arg.
* Right now, continuations dont take value stores. Is there some weird behavior that can come about if a value is mutated with `set!` and then when its time to read the continuation, a wrong value is propogated?
* In rust code, use a `KAddr` type for the KStore? Better typesafety.

## Bibliography ##

- Abstracting Abstract Machines (AAM)
- - Paper that introduces the idea of making an Abstract Interpreter out of a direct-style abstract machine. Has a good intro section describing how to go from CEK to an abstract time-stamped CESK*.
- - D. V. Horn and M. Might, “Abstracting Abstract Machines”.
- - Available online [here](http://matt.might.net/papers/vanhorn2010abstract.pdf)
- Pushdown Control-Flow Analysis for Free (P4F)
- - Continues on AAM to describe a good analysis that you can do for cheap. The background section was _very helpful_ in understanding how to better abstract an AM. Would recommend just the background section if you are still confused after AAM.
- - T. Gilray, S. Lyde, M. D. Adams, M. Might, and D. Van Horn, “Pushdown Control-Flow Analysis for Free,” Proceedings of the 43rd Annual ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages - POPL 2016, pp. 691–704, 2016, doi: 10.1145/2837614.2837631.
- - Available online [here](https://gilray.org/pdf/pushdown-for-free.pdf)
- Abstract Interpretation by Cousot & Cousot
- - The original paper on Abstract Interpretation. Pretty tough read, but helpful after a bunch of thorough readings!
- - P. Cousot and R. Cousot, “Abstract Interpretation: A Unified Lattice Model for Static Analysis of Programs by Construction or Approximation Of Fixpoints".
- - Available online [here](https://dl.acm.org/doi/10.1145/512950.512973) (search around for a PDF)
- Matt Might's Dissertation
- - This paper doesnt do AAMs but talks about Abstract Interpretation, CFA, and a few other topics. Also a helpful paper!
- - M. Might, “Environment analysis of higher-order languages” 2007.
- - Available online [here](http://matt.might.net/papers/might2007diss.pdf)

## License ##

MIT license! Enjoy!

Let me know if you use/enjoy this project, I would be very happy to hear it.
