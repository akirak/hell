# Hell: A Haskell shell

Here lies a prototype/experiment for the following question:
[can the normal Haskell REPL make a passable shell if it has file
completion and directory
awareness?](http://www.reddit.com/r/haskell/comments/1qzhce/using_haskell_to_write_deceptively_powerful/cdidvav?context=3)

It's a simple read-eval-print loop for Haskell that has some simple
awareness of the current directory and completion works. I whipped
this up in a few hours, it's only a couple hundred lines of code.

## What's it like?

It looks like this:

    Welcome to Hell!
    chris:~/$ ls
    Backups  Desktop    Downloads  Emacs  Mail  Pictures  Renoise  Samples
    Books	 Documents  Dropbox    Flash  Org   Projects  Repos    Scripts

It has some UNIX basics:

    chris:~/$ cd "Projects/hell/"
    chris:~/Projects/hell$ ls
    dist  examples	hell.cabal  LICENSE  README.md	src  TAGS
    chris:~/Projects/hell$ ls "-a"
    .  ..  dist  examples  .ghci  .git  .gitignore	hell.cabal LICENSE  README.md

All functions are based on
[shell-conduit](https://github.com/chrisdone/shell-conduit) and are
variadic. They are generated by taking all binaries in your PATH.

The only exception (so far) is `cd`. There is no binary called `cd` in
POSIX because it is a shell concept.

## How does it work?

It uses the GHC API (so please submit a pull request if it doesn't
work with your GHC version) and the Haskeline package to make a simple
read-eval-print loop, keeping track of any current directory
changes. The Haskeline package does completion at the prompt built-in.

It tries to run the line as an `IO a` statement:

    chris:~/$ cd "."

If that's the wrong
type, it runs it as a shell-conduit `Segment`:

    chris:~/$ ls $| grep "E"
    LICENSE
    README.md

Or finally it evaluates
it as an expression, printing the result with `print`:

    chris:~/$ 2 * 3
    forall a. GHC.Num.Num a => a
    6

I think it's pretty neat to have Haskell evaluation in your shell. I
often open GHCi to do little arithmetical calculations.

If it can't find any way to run it or print the value, it just
displays the type:

    chris:~/$ head
    forall a. [a] -> a

The commands of GHCi like `:t` and `:k` are not supported at this
time. Top-level bindings are not yet supported either.

It supports completion of function names, binaries and file names:

    chris:~/$ get
    getChar                    getfacl                    getZipSink
    getContents                gethostip                  getZipSource
    getContents                getkeycodes                getAppUserDataDirectory
    getLine                    getopt                     getCurrentDirectory
    getLine                    getpcaps                   getDirectoryContents
    getFpco                    gettext                    getHomeDirectory
    getafm                     gettextize                 getModificationTime
    getcap                     gettextsh                  getPermissions
    getconf                    getty                      getTemporaryDirectory
    geteltorito                getweb                     getUserDocumentsDirectory
    getent                     getZipConduit

## Why “Hell”? Surely a Haskell shell would be heaven!

It's an ironic name, like Little John. And who knows, a Haskell shell
_might_ be hell.

## You should add loads of custom syntax!

That's not going to happen. Hell is about plain Haskell.
