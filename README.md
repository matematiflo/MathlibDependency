# Lean Template repository

This sets up a basic Lean package on your machine, without a Mathlib dependency. If you want to add Mathlib as a dependency afterwards, see [Adding Mathlib](#adding-mathlib).

## Quickstart

If you already have [Lean](https://lean-lang.org/) installed on your machine, just clone the current repository, either using [GitHub Desktop]((https://docs.github.com/en/desktop/installing-and-authenticating-to-github-desktop/installing-github-desktop)) or via the command line

```console
git clone https://github.com/matematiflo/LeanTemplate.git
```

Then run the command

```console
lean HelloWorld.lean
```

It should return `Hello, world!`.

## Running a program

To try out the main function of the present package,  run the command line

```console
lake build Main
```

followed by

```console
lake env lean --run Main.lean
```

Alternately, you can compile `Main.lean` into an executable via the command

```console
lake build
```

and then run

```console
.build/bin/UserGreeting
```

It should return `Hello, User!`.

You can then go directly to the [Test file](#test-file) instructions.

## How to build this repo from scratch

1. Create a GitHub repo with an Apache 2.0 license.
2. Clone the repo on a machine which has Lean 4 already installed on it. Alternately, just create an empty directory `LeanTemplate` on your machine.
3. From a terminal, run the command `lake init greeting` (inside the cloned repo).
4. Still from a terminal, run the command `lake build`.

The last two steps are taken from the [Lean Manual](https://lean-lang.org/lean4/doc/setup.html#lake). They are enough for the command `./build/bin/greeting` to work and return `Hello, world!`. You do not need to have created a GitHub repo for this to work.

The `lake init greeting` command adds Lean to the current directory and creates a Lean package called `greeting`. You can see for instance that the files `lean-toolchain` and `lakefile.lean` have been created.

The `lake build` command then compiles the package into a binary called `greeting`, which is later run by the command `./build/bin/greeting`. If you do this, you will get a repo with a structure similar to this one, except for the `HelloWorld.lean`, `Test.lean` and `MathlibTest.lean` files.

However, the content of the files `Main.lean`, `Greeting/Basic.lean` and `lakefile.lean` have been slightly modified in the present repo:

- In `Main.lean`, the definition `IO.println s!"Hello, {hello}!"` has been replaced by `IO.println s!"Hello, {MyHello}!"`.
- In `Greeting/Basic.lean`, the declaration `def hello := "world"` has been replaced by `def MyHello := "User"
`.
- In `lakefile.lean`, the `lean_exe greeting` has been replaced by `lean_exe UserGreeting`.

## Test file

This repo contains an additional test file. You can see it at [Test.lean](Test.lean) and it contains the lines:

```lean
def main : IO Unit :=
  IO.println "Hello, world!"

#eval main

#eval 1 + 1

#check 3

def f (n : Nat) : Nat := 2 * n

#eval f 3

-- #print f
```

You can run `Test.lean` by running the command

```console
lean Test.lean
```

and it should return

```console
Hello, world!
2
3 : Nat
6
```

As you can see, there are two functions defined in the file `Test.lean`, one called `main` and the other one called `f`. When you run the file, the program returns everything that is located behind an `#eval` or `#check` command.

For instance, `#eval f 3` computes the value of `f` at the natural number `3`. Since `f` is the function from `Nat` to `Nat` sending `n` to `2 * n`, the return value for `n = 3` is `6`. You can also add `#check f` and see what happens.

If you edit the file to uncomment the line `#print f` by removing the `--` at the beginning of that line, you will see the following in your terminal:

```console
def f : Nat → Nat :=
fun n => 2 * n
```

This means that `f` is a function that takes a natural number `n`  to the natural number `2 * n`.

Finally, if instead of `lean Test.lean`, you run

```console
lean Test.lean --run
```

then the program returns `#eval main` one more time (at the very end). This enables you to not include an `#eval main` command if you want to run your function `main` only once and at the end, using the `--run` option.

## Installing Lean 4

You can install [Lean 4](https://github.com/leanprover/lean4) by following the instructions in one of the following sources:

- [https://lean-lang.org/lean4/doc/setup.html](https://lean-lang.org/lean4/doc/setup.html)
- [https://lean-lang.org/lean4/doc/quickstart.html](https://lean-lang.org/lean4/doc/quickstart.html)
- [https://lean-lang.org/download/](https://lean-lang.org/download/)
- [https://leanprover-community.github.io/get_started.html](https://leanprover-community.github.io/get_started.html)

You will need the Lean package manager called [elan](https://github.com/leanprover/elan), to install Lean. How you install elan depends on your operating system.

## On Mac OS

For a controlled installation of elan and Lean on Mac OS, see

> [https://leanprover-community.github.io/install/macos_details.html](https://leanprover-community.github.io/install/macos_details.html)

It will require you to install [Homebrew](https://brew.sh) by running the command line:

```console
/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
```

If the command `brew` is not recognized by your shell after the installation, see the [Troubleshooting](#homebrew-troubleshooting) section.

Otherwise, follow the steps below:

### Install elan

Install elan by running

```console
brew install elan-init
```

### Install the latest stable version of Lean

Install the latest stable version of Lean by running

```console
elan install stable
```

You may need to log off and log in again to your terminal again to make sure that the commands `lean` and `lake` become available. Check that this is indeed the case by running the command line

```console
lean --version
```

If the stable version is 4.2.0, then the command above should return

```console
Lean (version 4.2.0, commit 0d7051497ea0, Release)
```

If you want to make the installed version your default version, you can run

```console
elan default stable
```

As a matter of fact, if the stable version is not yet installed, the command above will also install it. You can check which versions (called *toolchains*) you have installed by running

```console
elan toolchain list
```

and which one one is the active toolchain by running

```console
elan show
```

In case of trouble, run `elan help`.

## Homebrew Troubleshooting

If you use `zsh` as a shell in your terminal app, after installing Homebrew, you will need to update your `PATH`. You can do so by following the steps below:

First, run the command line

```console
echo 'eval $(/opt/homebrew/bin/brew shellenv)' >> /Users/$USER/.zprofile
```

Then, run the command line

```console
eval $(/opt/homebrew/bin/brew shellenv)
```

You should be able to check that this has worked by typing in `brew help` in a terminal: this should now be recongnized by your shell.

## In Visual Studio Code

There is a [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) in [Visual Studio Code](https://code.visualstudio.com/download). It can install [various things](https://lean-lang.org/lean4/doc/quickstart.html) for you directly. And in general, VS Code is a powerful IDE to work on Lean code.

## Adding Mathlib

If you want to add Mathlib to the present project, follow the instructions below.

### Mathlib test file

This repo contains a file [MathlibTest.lean](MathlibTest.lean), whose contents are as follows.

```lean
import Mathlib.Data.List.Defs

#eval List.sum [1, 2, 3]
```

The function `List.sum` computes the sum of the members of a list. It is defined in `Mathlib.Data.List.Defs`, which is part of Mathlib.

If you run `lean MathibTest.lean` or even `lake env lean MathlibTest.lean` before installing Mathlib, you will see a list of error messages, starting with one that says `unknown package 'Mathlib'`).

To add a mathlib dependency, do the following.

### Modify `lakefile.lean`

Open the `lakefile.lean` file of the present repo and add to it the following lines

```lean
require mathlib from git "https://github.com/leanprover-community/mathlib4.git"
```

in between the `package` and `lean_lib` lines, to make it look like this:

```lean
package greeting where
  -- add package configuration options here

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

lean_lib Greeting where
  -- add library configuration options here
```

### Update the Lean version

Run the following command to replace your `lean-toolchain` file with the one used by the version of Mathlib that you are about to install:

```console
curl https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
```

### Install Mathlib

Run the command line

```console
lake update
```

This will update the Lean version and install a Mathlib dependency in your repo, creating a bunch of new files, including a directory called `lake-packages`.

### Download the compiled Mathlib libraries

Run the command line

```console
lake exe cache get
```

This downloads the Mathlib libraries, so you can avoid building Mathlib locally (which takes a long time). In principle, though, this can be done via the command `lake build MathlibTest.lean`.

You can consult the [Leanprover-community](https://leanprover-community.github.io) Wiki for more info:

> [Using mathlib4 as a dependency](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency)

### Run the Mathlib test file

After downloading the compiled Mathlib libraries using `lake exe cache get`, run the `MathlibTest.lean` file, via the command line

```console
lean MathlibTest.lean
```

This computes `List.sum [1, 2, 3]` and you should get the answer `6`, because `1 + 2 + 3 = 6`.
