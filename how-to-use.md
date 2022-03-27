# Scheme Compiler

## Scheme Compiler Final Project Grade: 99 🥳🥳

## About
This is my own "Scheme Compiler", written in OCaml 🐫 compiles Scheme code to x86-64 Assembly and runs on Linux based systems.

## How To Use
- First: you should have on your machine: nasm assembler, ocaml compiler.
- Second: clone or download this repo, create a .scm file at the same directory of this repo, you can call it any name you want, as example: `foo.scm`.
- Third: write some Scheme code in your `foo.scm` file.
- Fourth: open your Command Line or Terminal and change the directory to your cloned repo directory, then run this command `make clean foo` it's the easy way or just `make foo`, but then you should not forget to remove `"foo.s", "foo.o", "foo"` files for your next time coding. 
- Last thing: run your executable file `./foo`

```sh
echo "Hello World, This is Scheme" > foo.scm
make clean foo
./foo
```

## HAPPY SCHEME CODING 😉