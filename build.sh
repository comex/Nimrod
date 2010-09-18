#! /bin/sh
# Generated from niminst
# Template is in tools/buildsh.tmpl
# To regenerate run ``niminst csource`` or ``koch csource``
CC="gcc"
LINKER="gcc"
COMP_FLAGS="-w -O3 -fno-strict-aliasing"
LINK_FLAGS=""
# platform detection
ucpu=`uname -m`
uos=`uname`

# convert to lower case:
upcu=`echo $ucpu | tr "[:upper:]" "[:lower:]"`
uos=`echo $uos | tr "[:upper:]" "[:lower:]"`

case $uos in
  *linux* ) 
    myos="linux" 
    LINK_FLAGS="$LINK_FLAGS -ldl -lm"
    ;;
  *freebsd* ) 
    myos="freebsd"
    LINK_FLAGS="$LINK_FLAGS -lm"
    ;;
  *openbsd* )
    myos="openbsd" 
    LINK_FLAGS="$LINK_FLAGS -lm"
    ;;
  *netbsd* )
    myos="netbsd"
    LINK_FLAGS="$LINK_FLAGS -lm"
    ;;
  *darwin* ) 
    myos="macosx"
    LINK_FLAGS="$LINK_FLAGS -ldl -lm"
    if [ "$HOSTTYPE" = "x86_64" ] ; then
      ucpu="amd64"
    fi
    ;;
  *aix* )
    myos="aix"
    LINK_FLAGS="$LINK_FLAGS -ldl -lm"    
    ;;
  *solaris* | *sun* ) 
    myos="solaris"
    LINK_FLAGS="$LINK_FLAGS -ldl -lm"
    ;;
  *) 
    echo "Error: unknown operating system: $uos"
    exit 1
    ;;
esac

case $ucpu in
  *i386* | *i486* | *i586* | *i686* ) 
    mycpu="i386" ;;
  *amd*64* | *x86-64* | *x86_64* ) 
    mycpu="amd64" ;;
  *sparc*|*sun* ) 
    mycpu="sparc" ;;
  *power*|*Power* ) 
    mycpu="powerpc" ;;
  *mips* ) 
    mycpu="mips" ;;
  *) 
    echo "Error: unknown processor: $ucpu"
    exit 1
    ;;
esac

# call the compiler:

case $myos in
windows) 
  case $mycpu in
  i386)
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/system.c -o build/1_1/system.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/system.c -o build/1_1/system.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/winlean.c -o build/1_1/winlean.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/winlean.c -o build/1_1/winlean.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/times.c -o build/1_1/times.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/times.c -o build/1_1/times.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/lists.c -o build/1_1/lists.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/lists.c -o build/1_1/lists.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/nhashes.c -o build/1_1/nhashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/nhashes.c -o build/1_1/nhashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/nstrtabs.c -o build/1_1/nstrtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/nstrtabs.c -o build/1_1/nstrtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/options.c -o build/1_1/options.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/options.c -o build/1_1/options.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/msgs.c -o build/1_1/msgs.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/msgs.c -o build/1_1/msgs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/nversion.c -o build/1_1/nversion.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/nversion.c -o build/1_1/nversion.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/crc.c -o build/1_1/crc.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/crc.c -o build/1_1/crc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/platform.c -o build/1_1/platform.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/platform.c -o build/1_1/platform.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/ropes.c -o build/1_1/ropes.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/ropes.c -o build/1_1/ropes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/idents.c -o build/1_1/idents.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/idents.c -o build/1_1/idents.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/ast.c -o build/1_1/ast.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/ast.c -o build/1_1/ast.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/astalgo.c -o build/1_1/astalgo.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/astalgo.c -o build/1_1/astalgo.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/condsyms.c -o build/1_1/condsyms.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/condsyms.c -o build/1_1/condsyms.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/hashes.c -o build/1_1/hashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/hashes.c -o build/1_1/hashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/strtabs.c -o build/1_1/strtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/strtabs.c -o build/1_1/strtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/streams.c -o build/1_1/streams.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/streams.c -o build/1_1/streams.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/osproc.c -o build/1_1/osproc.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/osproc.c -o build/1_1/osproc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/extccomp.c -o build/1_1/extccomp.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/extccomp.c -o build/1_1/extccomp.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/wordrecg.c -o build/1_1/wordrecg.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/wordrecg.c -o build/1_1/wordrecg.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/commands.c -o build/1_1/commands.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/commands.c -o build/1_1/commands.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/llstream.c -o build/1_1/llstream.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/llstream.c -o build/1_1/llstream.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/lexbase.c -o build/1_1/lexbase.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/lexbase.c -o build/1_1/lexbase.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/scanner.c -o build/1_1/scanner.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/scanner.c -o build/1_1/scanner.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/nimconf.c -o build/1_1/nimconf.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/nimconf.c -o build/1_1/nimconf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/pnimsyn.c -o build/1_1/pnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/pnimsyn.c -o build/1_1/pnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/pbraces.c -o build/1_1/pbraces.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/pbraces.c -o build/1_1/pbraces.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/rnimsyn.c -o build/1_1/rnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/rnimsyn.c -o build/1_1/rnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/filters.c -o build/1_1/filters.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/filters.c -o build/1_1/filters.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/ptmplsyn.c -o build/1_1/ptmplsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/ptmplsyn.c -o build/1_1/ptmplsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/syntaxes.c -o build/1_1/syntaxes.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/syntaxes.c -o build/1_1/syntaxes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/rodread.c -o build/1_1/rodread.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/rodread.c -o build/1_1/rodread.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/trees.c -o build/1_1/trees.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/trees.c -o build/1_1/trees.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/types.c -o build/1_1/types.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/types.c -o build/1_1/types.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/math.c -o build/1_1/math.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/math.c -o build/1_1/math.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/magicsys.c -o build/1_1/magicsys.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/magicsys.c -o build/1_1/magicsys.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/bitsets.c -o build/1_1/bitsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/bitsets.c -o build/1_1/bitsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/nimsets.c -o build/1_1/nimsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/nimsets.c -o build/1_1/nimsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/passes.c -o build/1_1/passes.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/passes.c -o build/1_1/passes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/treetab.c -o build/1_1/treetab.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/treetab.c -o build/1_1/treetab.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/semdata.c -o build/1_1/semdata.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/semdata.c -o build/1_1/semdata.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/lookups.c -o build/1_1/lookups.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/lookups.c -o build/1_1/lookups.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/importer.c -o build/1_1/importer.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/importer.c -o build/1_1/importer.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/rodwrite.c -o build/1_1/rodwrite.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/rodwrite.c -o build/1_1/rodwrite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/semfold.c -o build/1_1/semfold.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/semfold.c -o build/1_1/semfold.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/evals.c -o build/1_1/evals.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/evals.c -o build/1_1/evals.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/procfind.c -o build/1_1/procfind.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/procfind.c -o build/1_1/procfind.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/pragmas.c -o build/1_1/pragmas.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/pragmas.c -o build/1_1/pragmas.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/sem.c -o build/1_1/sem.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/sem.c -o build/1_1/sem.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/rst.c -o build/1_1/rst.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/rst.c -o build/1_1/rst.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/highlite.c -o build/1_1/highlite.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/highlite.c -o build/1_1/highlite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/docgen.c -o build/1_1/docgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/docgen.c -o build/1_1/docgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/ccgutils.c -o build/1_1/ccgutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/ccgutils.c -o build/1_1/ccgutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/cgmeth.c -o build/1_1/cgmeth.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/cgmeth.c -o build/1_1/cgmeth.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/cgen.c -o build/1_1/cgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/cgen.c -o build/1_1/cgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/ecmasgen.c -o build/1_1/ecmasgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/ecmasgen.c -o build/1_1/ecmasgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/interact.c -o build/1_1/interact.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/interact.c -o build/1_1/interact.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/passaux.c -o build/1_1/passaux.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/passaux.c -o build/1_1/passaux.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/depends.c -o build/1_1/depends.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/depends.c -o build/1_1/depends.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/transf.c -o build/1_1/transf.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/transf.c -o build/1_1/transf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/main.c -o build/1_1/main.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/main.c -o build/1_1/main.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/parseopt.c -o build/1_1/parseopt.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/parseopt.c -o build/1_1/parseopt.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/nim__dat.c -o build/1_1/nim__dat.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/nim__dat.c -o build/1_1/nim__dat.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/parseutils.c -o build/1_1/parseutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/parseutils.c -o build/1_1/parseutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/strutils.c -o build/1_1/strutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/strutils.c -o build/1_1/strutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/os.c -o build/1_1/os.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/os.c -o build/1_1/os.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/nimrod.c -o build/1_1/nimrod.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/nimrod.c -o build/1_1/nimrod.o || exit 1
    echo "$LINKER $LINK_FLAGS -o bin/nimrod  \
build/1_1/system.o \
build/1_1/winlean.o \
build/1_1/times.o \
build/1_1/lists.o \
build/1_1/nhashes.o \
build/1_1/nstrtabs.o \
build/1_1/options.o \
build/1_1/msgs.o \
build/1_1/nversion.o \
build/1_1/crc.o \
build/1_1/platform.o \
build/1_1/ropes.o \
build/1_1/idents.o \
build/1_1/ast.o \
build/1_1/astalgo.o \
build/1_1/condsyms.o \
build/1_1/hashes.o \
build/1_1/strtabs.o \
build/1_1/streams.o \
build/1_1/osproc.o \
build/1_1/extccomp.o \
build/1_1/wordrecg.o \
build/1_1/commands.o \
build/1_1/llstream.o \
build/1_1/lexbase.o \
build/1_1/scanner.o \
build/1_1/nimconf.o \
build/1_1/pnimsyn.o \
build/1_1/pbraces.o \
build/1_1/rnimsyn.o \
build/1_1/filters.o \
build/1_1/ptmplsyn.o \
build/1_1/syntaxes.o \
build/1_1/rodread.o \
build/1_1/trees.o \
build/1_1/types.o \
build/1_1/math.o \
build/1_1/magicsys.o \
build/1_1/bitsets.o \
build/1_1/nimsets.o \
build/1_1/passes.o \
build/1_1/treetab.o \
build/1_1/semdata.o \
build/1_1/lookups.o \
build/1_1/importer.o \
build/1_1/rodwrite.o \
build/1_1/semfold.o \
build/1_1/evals.o \
build/1_1/procfind.o \
build/1_1/pragmas.o \
build/1_1/sem.o \
build/1_1/rst.o \
build/1_1/highlite.o \
build/1_1/docgen.o \
build/1_1/ccgutils.o \
build/1_1/cgmeth.o \
build/1_1/cgen.o \
build/1_1/ecmasgen.o \
build/1_1/interact.o \
build/1_1/passaux.o \
build/1_1/depends.o \
build/1_1/transf.o \
build/1_1/main.o \
build/1_1/parseopt.o \
build/1_1/nim__dat.o \
build/1_1/parseutils.o \
build/1_1/strutils.o \
build/1_1/os.o \
build/1_1/nimrod.o"
    $LINKER $LINK_FLAGS -o bin/nimrod  \
build/1_1/system.o \
build/1_1/winlean.o \
build/1_1/times.o \
build/1_1/lists.o \
build/1_1/nhashes.o \
build/1_1/nstrtabs.o \
build/1_1/options.o \
build/1_1/msgs.o \
build/1_1/nversion.o \
build/1_1/crc.o \
build/1_1/platform.o \
build/1_1/ropes.o \
build/1_1/idents.o \
build/1_1/ast.o \
build/1_1/astalgo.o \
build/1_1/condsyms.o \
build/1_1/hashes.o \
build/1_1/strtabs.o \
build/1_1/streams.o \
build/1_1/osproc.o \
build/1_1/extccomp.o \
build/1_1/wordrecg.o \
build/1_1/commands.o \
build/1_1/llstream.o \
build/1_1/lexbase.o \
build/1_1/scanner.o \
build/1_1/nimconf.o \
build/1_1/pnimsyn.o \
build/1_1/pbraces.o \
build/1_1/rnimsyn.o \
build/1_1/filters.o \
build/1_1/ptmplsyn.o \
build/1_1/syntaxes.o \
build/1_1/rodread.o \
build/1_1/trees.o \
build/1_1/types.o \
build/1_1/math.o \
build/1_1/magicsys.o \
build/1_1/bitsets.o \
build/1_1/nimsets.o \
build/1_1/passes.o \
build/1_1/treetab.o \
build/1_1/semdata.o \
build/1_1/lookups.o \
build/1_1/importer.o \
build/1_1/rodwrite.o \
build/1_1/semfold.o \
build/1_1/evals.o \
build/1_1/procfind.o \
build/1_1/pragmas.o \
build/1_1/sem.o \
build/1_1/rst.o \
build/1_1/highlite.o \
build/1_1/docgen.o \
build/1_1/ccgutils.o \
build/1_1/cgmeth.o \
build/1_1/cgen.o \
build/1_1/ecmasgen.o \
build/1_1/interact.o \
build/1_1/passaux.o \
build/1_1/depends.o \
build/1_1/transf.o \
build/1_1/main.o \
build/1_1/parseopt.o \
build/1_1/nim__dat.o \
build/1_1/parseutils.o \
build/1_1/strutils.o \
build/1_1/os.o \
build/1_1/nimrod.o || exit 1
    ;;
  amd64)
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/system.c -o build/1_2/system.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/system.c -o build/1_2/system.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/winlean.c -o build/1_2/winlean.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/winlean.c -o build/1_2/winlean.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/times.c -o build/1_2/times.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/times.c -o build/1_2/times.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/lists.c -o build/1_2/lists.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/lists.c -o build/1_2/lists.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/nhashes.c -o build/1_2/nhashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/nhashes.c -o build/1_2/nhashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/nstrtabs.c -o build/1_2/nstrtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/nstrtabs.c -o build/1_2/nstrtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/options.c -o build/1_2/options.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/options.c -o build/1_2/options.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/msgs.c -o build/1_2/msgs.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/msgs.c -o build/1_2/msgs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/nversion.c -o build/1_2/nversion.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/nversion.c -o build/1_2/nversion.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/crc.c -o build/1_2/crc.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/crc.c -o build/1_2/crc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/platform.c -o build/1_2/platform.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/platform.c -o build/1_2/platform.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/ropes.c -o build/1_2/ropes.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/ropes.c -o build/1_2/ropes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/idents.c -o build/1_2/idents.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/idents.c -o build/1_2/idents.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/ast.c -o build/1_2/ast.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/ast.c -o build/1_2/ast.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/astalgo.c -o build/1_2/astalgo.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/astalgo.c -o build/1_2/astalgo.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/condsyms.c -o build/1_2/condsyms.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/condsyms.c -o build/1_2/condsyms.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/hashes.c -o build/1_2/hashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/hashes.c -o build/1_2/hashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/strtabs.c -o build/1_2/strtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/strtabs.c -o build/1_2/strtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/streams.c -o build/1_2/streams.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/streams.c -o build/1_2/streams.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/osproc.c -o build/1_2/osproc.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/osproc.c -o build/1_2/osproc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/extccomp.c -o build/1_2/extccomp.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/extccomp.c -o build/1_2/extccomp.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/wordrecg.c -o build/1_2/wordrecg.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/wordrecg.c -o build/1_2/wordrecg.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/commands.c -o build/1_2/commands.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/commands.c -o build/1_2/commands.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/llstream.c -o build/1_2/llstream.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/llstream.c -o build/1_2/llstream.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/lexbase.c -o build/1_2/lexbase.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/lexbase.c -o build/1_2/lexbase.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/scanner.c -o build/1_2/scanner.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/scanner.c -o build/1_2/scanner.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/nimconf.c -o build/1_2/nimconf.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/nimconf.c -o build/1_2/nimconf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/pnimsyn.c -o build/1_2/pnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/pnimsyn.c -o build/1_2/pnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/pbraces.c -o build/1_2/pbraces.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/pbraces.c -o build/1_2/pbraces.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/rnimsyn.c -o build/1_2/rnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/rnimsyn.c -o build/1_2/rnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/filters.c -o build/1_2/filters.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/filters.c -o build/1_2/filters.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/ptmplsyn.c -o build/1_2/ptmplsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/ptmplsyn.c -o build/1_2/ptmplsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/syntaxes.c -o build/1_2/syntaxes.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/syntaxes.c -o build/1_2/syntaxes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/rodread.c -o build/1_2/rodread.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/rodread.c -o build/1_2/rodread.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/trees.c -o build/1_2/trees.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/trees.c -o build/1_2/trees.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/types.c -o build/1_2/types.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/types.c -o build/1_2/types.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/math.c -o build/1_2/math.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/math.c -o build/1_2/math.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/magicsys.c -o build/1_2/magicsys.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/magicsys.c -o build/1_2/magicsys.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/bitsets.c -o build/1_2/bitsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/bitsets.c -o build/1_2/bitsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/nimsets.c -o build/1_2/nimsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/nimsets.c -o build/1_2/nimsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/passes.c -o build/1_2/passes.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/passes.c -o build/1_2/passes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/treetab.c -o build/1_2/treetab.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/treetab.c -o build/1_2/treetab.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/semdata.c -o build/1_2/semdata.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/semdata.c -o build/1_2/semdata.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/lookups.c -o build/1_2/lookups.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/lookups.c -o build/1_2/lookups.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/importer.c -o build/1_2/importer.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/importer.c -o build/1_2/importer.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/rodwrite.c -o build/1_2/rodwrite.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/rodwrite.c -o build/1_2/rodwrite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/semfold.c -o build/1_2/semfold.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/semfold.c -o build/1_2/semfold.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/evals.c -o build/1_2/evals.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/evals.c -o build/1_2/evals.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/procfind.c -o build/1_2/procfind.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/procfind.c -o build/1_2/procfind.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/pragmas.c -o build/1_2/pragmas.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/pragmas.c -o build/1_2/pragmas.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/sem.c -o build/1_2/sem.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/sem.c -o build/1_2/sem.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/rst.c -o build/1_2/rst.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/rst.c -o build/1_2/rst.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/highlite.c -o build/1_2/highlite.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/highlite.c -o build/1_2/highlite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/docgen.c -o build/1_2/docgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/docgen.c -o build/1_2/docgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/ccgutils.c -o build/1_2/ccgutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/ccgutils.c -o build/1_2/ccgutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/cgmeth.c -o build/1_2/cgmeth.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/cgmeth.c -o build/1_2/cgmeth.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/cgen.c -o build/1_2/cgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/cgen.c -o build/1_2/cgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/ecmasgen.c -o build/1_2/ecmasgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/ecmasgen.c -o build/1_2/ecmasgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/interact.c -o build/1_2/interact.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/interact.c -o build/1_2/interact.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/passaux.c -o build/1_2/passaux.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/passaux.c -o build/1_2/passaux.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/depends.c -o build/1_2/depends.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/depends.c -o build/1_2/depends.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/transf.c -o build/1_2/transf.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/transf.c -o build/1_2/transf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/main.c -o build/1_2/main.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/main.c -o build/1_2/main.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/parseopt.c -o build/1_2/parseopt.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/parseopt.c -o build/1_2/parseopt.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/nim__dat.c -o build/1_2/nim__dat.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/nim__dat.c -o build/1_2/nim__dat.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/parseutils.c -o build/1_2/parseutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/parseutils.c -o build/1_2/parseutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/strutils.c -o build/1_2/strutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/strutils.c -o build/1_2/strutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/os.c -o build/1_2/os.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/os.c -o build/1_2/os.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_2/nimrod.c -o build/1_2/nimrod.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_2/nimrod.c -o build/1_2/nimrod.o || exit 1
    echo "$LINKER $LINK_FLAGS -o bin/nimrod  \
build/1_2/system.o \
build/1_2/winlean.o \
build/1_2/times.o \
build/1_2/lists.o \
build/1_2/nhashes.o \
build/1_2/nstrtabs.o \
build/1_2/options.o \
build/1_2/msgs.o \
build/1_2/nversion.o \
build/1_2/crc.o \
build/1_2/platform.o \
build/1_2/ropes.o \
build/1_2/idents.o \
build/1_2/ast.o \
build/1_2/astalgo.o \
build/1_2/condsyms.o \
build/1_2/hashes.o \
build/1_2/strtabs.o \
build/1_2/streams.o \
build/1_2/osproc.o \
build/1_2/extccomp.o \
build/1_2/wordrecg.o \
build/1_2/commands.o \
build/1_2/llstream.o \
build/1_2/lexbase.o \
build/1_2/scanner.o \
build/1_2/nimconf.o \
build/1_2/pnimsyn.o \
build/1_2/pbraces.o \
build/1_2/rnimsyn.o \
build/1_2/filters.o \
build/1_2/ptmplsyn.o \
build/1_2/syntaxes.o \
build/1_2/rodread.o \
build/1_2/trees.o \
build/1_2/types.o \
build/1_2/math.o \
build/1_2/magicsys.o \
build/1_2/bitsets.o \
build/1_2/nimsets.o \
build/1_2/passes.o \
build/1_2/treetab.o \
build/1_2/semdata.o \
build/1_2/lookups.o \
build/1_2/importer.o \
build/1_2/rodwrite.o \
build/1_2/semfold.o \
build/1_2/evals.o \
build/1_2/procfind.o \
build/1_2/pragmas.o \
build/1_2/sem.o \
build/1_2/rst.o \
build/1_2/highlite.o \
build/1_2/docgen.o \
build/1_2/ccgutils.o \
build/1_2/cgmeth.o \
build/1_2/cgen.o \
build/1_2/ecmasgen.o \
build/1_2/interact.o \
build/1_2/passaux.o \
build/1_2/depends.o \
build/1_2/transf.o \
build/1_2/main.o \
build/1_2/parseopt.o \
build/1_2/nim__dat.o \
build/1_2/parseutils.o \
build/1_2/strutils.o \
build/1_2/os.o \
build/1_2/nimrod.o"
    $LINKER $LINK_FLAGS -o bin/nimrod  \
build/1_2/system.o \
build/1_2/winlean.o \
build/1_2/times.o \
build/1_2/lists.o \
build/1_2/nhashes.o \
build/1_2/nstrtabs.o \
build/1_2/options.o \
build/1_2/msgs.o \
build/1_2/nversion.o \
build/1_2/crc.o \
build/1_2/platform.o \
build/1_2/ropes.o \
build/1_2/idents.o \
build/1_2/ast.o \
build/1_2/astalgo.o \
build/1_2/condsyms.o \
build/1_2/hashes.o \
build/1_2/strtabs.o \
build/1_2/streams.o \
build/1_2/osproc.o \
build/1_2/extccomp.o \
build/1_2/wordrecg.o \
build/1_2/commands.o \
build/1_2/llstream.o \
build/1_2/lexbase.o \
build/1_2/scanner.o \
build/1_2/nimconf.o \
build/1_2/pnimsyn.o \
build/1_2/pbraces.o \
build/1_2/rnimsyn.o \
build/1_2/filters.o \
build/1_2/ptmplsyn.o \
build/1_2/syntaxes.o \
build/1_2/rodread.o \
build/1_2/trees.o \
build/1_2/types.o \
build/1_2/math.o \
build/1_2/magicsys.o \
build/1_2/bitsets.o \
build/1_2/nimsets.o \
build/1_2/passes.o \
build/1_2/treetab.o \
build/1_2/semdata.o \
build/1_2/lookups.o \
build/1_2/importer.o \
build/1_2/rodwrite.o \
build/1_2/semfold.o \
build/1_2/evals.o \
build/1_2/procfind.o \
build/1_2/pragmas.o \
build/1_2/sem.o \
build/1_2/rst.o \
build/1_2/highlite.o \
build/1_2/docgen.o \
build/1_2/ccgutils.o \
build/1_2/cgmeth.o \
build/1_2/cgen.o \
build/1_2/ecmasgen.o \
build/1_2/interact.o \
build/1_2/passaux.o \
build/1_2/depends.o \
build/1_2/transf.o \
build/1_2/main.o \
build/1_2/parseopt.o \
build/1_2/nim__dat.o \
build/1_2/parseutils.o \
build/1_2/strutils.o \
build/1_2/os.o \
build/1_2/nimrod.o || exit 1
    ;;
  powerpc)
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/system.c -o build/1_1/system.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/system.c -o build/1_1/system.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/winlean.c -o build/1_1/winlean.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/winlean.c -o build/1_1/winlean.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/times.c -o build/1_1/times.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/times.c -o build/1_1/times.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/lists.c -o build/1_1/lists.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/lists.c -o build/1_1/lists.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/nhashes.c -o build/1_1/nhashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/nhashes.c -o build/1_1/nhashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/nstrtabs.c -o build/1_1/nstrtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/nstrtabs.c -o build/1_1/nstrtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_3/options.c -o build/1_3/options.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_3/options.c -o build/1_3/options.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_3/msgs.c -o build/1_3/msgs.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_3/msgs.c -o build/1_3/msgs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/nversion.c -o build/1_1/nversion.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/nversion.c -o build/1_1/nversion.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/crc.c -o build/1_1/crc.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/crc.c -o build/1_1/crc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_3/platform.c -o build/1_3/platform.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_3/platform.c -o build/1_3/platform.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/ropes.c -o build/1_1/ropes.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/ropes.c -o build/1_1/ropes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/idents.c -o build/1_1/idents.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/idents.c -o build/1_1/idents.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_3/ast.c -o build/1_3/ast.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_3/ast.c -o build/1_3/ast.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/astalgo.c -o build/1_1/astalgo.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/astalgo.c -o build/1_1/astalgo.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/condsyms.c -o build/1_1/condsyms.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/condsyms.c -o build/1_1/condsyms.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/hashes.c -o build/1_1/hashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/hashes.c -o build/1_1/hashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/strtabs.c -o build/1_1/strtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/strtabs.c -o build/1_1/strtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/streams.c -o build/1_1/streams.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/streams.c -o build/1_1/streams.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/osproc.c -o build/1_1/osproc.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/osproc.c -o build/1_1/osproc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_3/extccomp.c -o build/1_3/extccomp.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_3/extccomp.c -o build/1_3/extccomp.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/wordrecg.c -o build/1_1/wordrecg.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/wordrecg.c -o build/1_1/wordrecg.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_3/commands.c -o build/1_3/commands.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_3/commands.c -o build/1_3/commands.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/llstream.c -o build/1_1/llstream.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/llstream.c -o build/1_1/llstream.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/lexbase.c -o build/1_1/lexbase.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/lexbase.c -o build/1_1/lexbase.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/scanner.c -o build/1_1/scanner.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/scanner.c -o build/1_1/scanner.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/nimconf.c -o build/1_1/nimconf.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/nimconf.c -o build/1_1/nimconf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/pnimsyn.c -o build/1_1/pnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/pnimsyn.c -o build/1_1/pnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/pbraces.c -o build/1_1/pbraces.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/pbraces.c -o build/1_1/pbraces.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/rnimsyn.c -o build/1_1/rnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/rnimsyn.c -o build/1_1/rnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/filters.c -o build/1_1/filters.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/filters.c -o build/1_1/filters.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/ptmplsyn.c -o build/1_1/ptmplsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/ptmplsyn.c -o build/1_1/ptmplsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/syntaxes.c -o build/1_1/syntaxes.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/syntaxes.c -o build/1_1/syntaxes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/rodread.c -o build/1_1/rodread.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/rodread.c -o build/1_1/rodread.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/trees.c -o build/1_1/trees.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/trees.c -o build/1_1/trees.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_3/types.c -o build/1_3/types.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_3/types.c -o build/1_3/types.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/math.c -o build/1_1/math.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/math.c -o build/1_1/math.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/magicsys.c -o build/1_1/magicsys.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/magicsys.c -o build/1_1/magicsys.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/bitsets.c -o build/1_1/bitsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/bitsets.c -o build/1_1/bitsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/nimsets.c -o build/1_1/nimsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/nimsets.c -o build/1_1/nimsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_3/passes.c -o build/1_3/passes.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_3/passes.c -o build/1_3/passes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/treetab.c -o build/1_1/treetab.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/treetab.c -o build/1_1/treetab.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/semdata.c -o build/1_1/semdata.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/semdata.c -o build/1_1/semdata.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_3/lookups.c -o build/1_3/lookups.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_3/lookups.c -o build/1_3/lookups.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_3/importer.c -o build/1_3/importer.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_3/importer.c -o build/1_3/importer.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_3/rodwrite.c -o build/1_3/rodwrite.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_3/rodwrite.c -o build/1_3/rodwrite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_3/semfold.c -o build/1_3/semfold.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_3/semfold.c -o build/1_3/semfold.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_3/evals.c -o build/1_3/evals.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_3/evals.c -o build/1_3/evals.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/procfind.c -o build/1_1/procfind.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/procfind.c -o build/1_1/procfind.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_3/pragmas.c -o build/1_3/pragmas.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_3/pragmas.c -o build/1_3/pragmas.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_3/sem.c -o build/1_3/sem.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_3/sem.c -o build/1_3/sem.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/rst.c -o build/1_1/rst.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/rst.c -o build/1_1/rst.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/highlite.c -o build/1_1/highlite.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/highlite.c -o build/1_1/highlite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/docgen.c -o build/1_1/docgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/docgen.c -o build/1_1/docgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/ccgutils.c -o build/1_1/ccgutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/ccgutils.c -o build/1_1/ccgutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_3/cgmeth.c -o build/1_3/cgmeth.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_3/cgmeth.c -o build/1_3/cgmeth.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_3/cgen.c -o build/1_3/cgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_3/cgen.c -o build/1_3/cgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_3/ecmasgen.c -o build/1_3/ecmasgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_3/ecmasgen.c -o build/1_3/ecmasgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/interact.c -o build/1_1/interact.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/interact.c -o build/1_1/interact.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/passaux.c -o build/1_1/passaux.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/passaux.c -o build/1_1/passaux.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/depends.c -o build/1_1/depends.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/depends.c -o build/1_1/depends.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_3/transf.c -o build/1_3/transf.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_3/transf.c -o build/1_3/transf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/main.c -o build/1_1/main.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/main.c -o build/1_1/main.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/parseopt.c -o build/1_1/parseopt.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/parseopt.c -o build/1_1/parseopt.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/nim__dat.c -o build/1_1/nim__dat.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/nim__dat.c -o build/1_1/nim__dat.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/parseutils.c -o build/1_1/parseutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/parseutils.c -o build/1_1/parseutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/strutils.c -o build/1_1/strutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/strutils.c -o build/1_1/strutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_1/os.c -o build/1_1/os.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_1/os.c -o build/1_1/os.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/1_3/nimrod.c -o build/1_3/nimrod.o"
    $CC $COMP_FLAGS -Ibuild -c build/1_3/nimrod.c -o build/1_3/nimrod.o || exit 1
    echo "$LINKER $LINK_FLAGS -o bin/nimrod  \
build/1_1/system.o \
build/1_1/winlean.o \
build/1_1/times.o \
build/1_1/lists.o \
build/1_1/nhashes.o \
build/1_1/nstrtabs.o \
build/1_3/options.o \
build/1_3/msgs.o \
build/1_1/nversion.o \
build/1_1/crc.o \
build/1_3/platform.o \
build/1_1/ropes.o \
build/1_1/idents.o \
build/1_3/ast.o \
build/1_1/astalgo.o \
build/1_1/condsyms.o \
build/1_1/hashes.o \
build/1_1/strtabs.o \
build/1_1/streams.o \
build/1_1/osproc.o \
build/1_3/extccomp.o \
build/1_1/wordrecg.o \
build/1_3/commands.o \
build/1_1/llstream.o \
build/1_1/lexbase.o \
build/1_1/scanner.o \
build/1_1/nimconf.o \
build/1_1/pnimsyn.o \
build/1_1/pbraces.o \
build/1_1/rnimsyn.o \
build/1_1/filters.o \
build/1_1/ptmplsyn.o \
build/1_1/syntaxes.o \
build/1_1/rodread.o \
build/1_1/trees.o \
build/1_3/types.o \
build/1_1/math.o \
build/1_1/magicsys.o \
build/1_1/bitsets.o \
build/1_1/nimsets.o \
build/1_3/passes.o \
build/1_1/treetab.o \
build/1_1/semdata.o \
build/1_3/lookups.o \
build/1_3/importer.o \
build/1_3/rodwrite.o \
build/1_3/semfold.o \
build/1_3/evals.o \
build/1_1/procfind.o \
build/1_3/pragmas.o \
build/1_3/sem.o \
build/1_1/rst.o \
build/1_1/highlite.o \
build/1_1/docgen.o \
build/1_1/ccgutils.o \
build/1_3/cgmeth.o \
build/1_3/cgen.o \
build/1_3/ecmasgen.o \
build/1_1/interact.o \
build/1_1/passaux.o \
build/1_1/depends.o \
build/1_3/transf.o \
build/1_1/main.o \
build/1_1/parseopt.o \
build/1_1/nim__dat.o \
build/1_1/parseutils.o \
build/1_1/strutils.o \
build/1_1/os.o \
build/1_3/nimrod.o"
    $LINKER $LINK_FLAGS -o bin/nimrod  \
build/1_1/system.o \
build/1_1/winlean.o \
build/1_1/times.o \
build/1_1/lists.o \
build/1_1/nhashes.o \
build/1_1/nstrtabs.o \
build/1_3/options.o \
build/1_3/msgs.o \
build/1_1/nversion.o \
build/1_1/crc.o \
build/1_3/platform.o \
build/1_1/ropes.o \
build/1_1/idents.o \
build/1_3/ast.o \
build/1_1/astalgo.o \
build/1_1/condsyms.o \
build/1_1/hashes.o \
build/1_1/strtabs.o \
build/1_1/streams.o \
build/1_1/osproc.o \
build/1_3/extccomp.o \
build/1_1/wordrecg.o \
build/1_3/commands.o \
build/1_1/llstream.o \
build/1_1/lexbase.o \
build/1_1/scanner.o \
build/1_1/nimconf.o \
build/1_1/pnimsyn.o \
build/1_1/pbraces.o \
build/1_1/rnimsyn.o \
build/1_1/filters.o \
build/1_1/ptmplsyn.o \
build/1_1/syntaxes.o \
build/1_1/rodread.o \
build/1_1/trees.o \
build/1_3/types.o \
build/1_1/math.o \
build/1_1/magicsys.o \
build/1_1/bitsets.o \
build/1_1/nimsets.o \
build/1_3/passes.o \
build/1_1/treetab.o \
build/1_1/semdata.o \
build/1_3/lookups.o \
build/1_3/importer.o \
build/1_3/rodwrite.o \
build/1_3/semfold.o \
build/1_3/evals.o \
build/1_1/procfind.o \
build/1_3/pragmas.o \
build/1_3/sem.o \
build/1_1/rst.o \
build/1_1/highlite.o \
build/1_1/docgen.o \
build/1_1/ccgutils.o \
build/1_3/cgmeth.o \
build/1_3/cgen.o \
build/1_3/ecmasgen.o \
build/1_1/interact.o \
build/1_1/passaux.o \
build/1_1/depends.o \
build/1_3/transf.o \
build/1_1/main.o \
build/1_1/parseopt.o \
build/1_1/nim__dat.o \
build/1_1/parseutils.o \
build/1_1/strutils.o \
build/1_1/os.o \
build/1_3/nimrod.o || exit 1
    ;;
  *)
    echo "Error: no C code generated for: [$myos: $mycpu]"
    exit 1
    ;;
  esac
  ;;
linux) 
  case $mycpu in
  i386)
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/system.c -o build/2_1/system.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/system.c -o build/2_1/system.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/times.c -o build/2_1/times.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/times.c -o build/2_1/times.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/posix.c -o build/2_1/posix.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/posix.c -o build/2_1/posix.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lists.c -o build/2_1/lists.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lists.c -o build/2_1/lists.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nhashes.c -o build/2_1/nhashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nhashes.c -o build/2_1/nhashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nstrtabs.c -o build/2_1/nstrtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nstrtabs.c -o build/2_1/nstrtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/options.c -o build/2_1/options.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/options.c -o build/2_1/options.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/msgs.c -o build/2_1/msgs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/msgs.c -o build/2_1/msgs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nversion.c -o build/2_1/nversion.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nversion.c -o build/2_1/nversion.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/crc.c -o build/2_1/crc.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/crc.c -o build/2_1/crc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/platform.c -o build/2_1/platform.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/platform.c -o build/2_1/platform.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ropes.c -o build/2_1/ropes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ropes.c -o build/2_1/ropes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/idents.c -o build/2_1/idents.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/idents.c -o build/2_1/idents.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ast.c -o build/2_1/ast.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ast.c -o build/2_1/ast.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/astalgo.c -o build/2_1/astalgo.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/astalgo.c -o build/2_1/astalgo.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/condsyms.c -o build/2_1/condsyms.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/condsyms.c -o build/2_1/condsyms.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/hashes.c -o build/2_1/hashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/hashes.c -o build/2_1/hashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/strtabs.c -o build/2_1/strtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/strtabs.c -o build/2_1/strtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/streams.c -o build/2_1/streams.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/streams.c -o build/2_1/streams.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/osproc.c -o build/2_1/osproc.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/osproc.c -o build/2_1/osproc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/extccomp.c -o build/2_1/extccomp.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/extccomp.c -o build/2_1/extccomp.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/wordrecg.c -o build/2_1/wordrecg.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/wordrecg.c -o build/2_1/wordrecg.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/commands.c -o build/2_1/commands.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/commands.c -o build/2_1/commands.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/llstream.c -o build/2_1/llstream.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/llstream.c -o build/2_1/llstream.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lexbase.c -o build/2_1/lexbase.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lexbase.c -o build/2_1/lexbase.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/scanner.c -o build/2_1/scanner.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/scanner.c -o build/2_1/scanner.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nimconf.c -o build/2_1/nimconf.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nimconf.c -o build/2_1/nimconf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pnimsyn.c -o build/2_1/pnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pnimsyn.c -o build/2_1/pnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pbraces.c -o build/2_1/pbraces.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pbraces.c -o build/2_1/pbraces.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rnimsyn.c -o build/2_1/rnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rnimsyn.c -o build/2_1/rnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/filters.c -o build/2_1/filters.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/filters.c -o build/2_1/filters.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ptmplsyn.c -o build/2_1/ptmplsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ptmplsyn.c -o build/2_1/ptmplsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/syntaxes.c -o build/2_1/syntaxes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/syntaxes.c -o build/2_1/syntaxes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rodread.c -o build/2_1/rodread.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rodread.c -o build/2_1/rodread.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/trees.c -o build/2_1/trees.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/trees.c -o build/2_1/trees.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/types.c -o build/2_1/types.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/types.c -o build/2_1/types.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/math.c -o build/2_1/math.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/math.c -o build/2_1/math.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/magicsys.c -o build/2_1/magicsys.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/magicsys.c -o build/2_1/magicsys.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/bitsets.c -o build/2_1/bitsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/bitsets.c -o build/2_1/bitsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nimsets.c -o build/2_1/nimsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nimsets.c -o build/2_1/nimsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/passes.c -o build/2_1/passes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/passes.c -o build/2_1/passes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/treetab.c -o build/2_1/treetab.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/treetab.c -o build/2_1/treetab.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/semdata.c -o build/2_1/semdata.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/semdata.c -o build/2_1/semdata.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lookups.c -o build/2_1/lookups.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lookups.c -o build/2_1/lookups.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/importer.c -o build/2_1/importer.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/importer.c -o build/2_1/importer.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rodwrite.c -o build/2_1/rodwrite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rodwrite.c -o build/2_1/rodwrite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/semfold.c -o build/2_1/semfold.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/semfold.c -o build/2_1/semfold.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/evals.c -o build/2_1/evals.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/evals.c -o build/2_1/evals.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/procfind.c -o build/2_1/procfind.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/procfind.c -o build/2_1/procfind.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pragmas.c -o build/2_1/pragmas.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pragmas.c -o build/2_1/pragmas.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/sem.c -o build/2_1/sem.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/sem.c -o build/2_1/sem.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rst.c -o build/2_1/rst.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rst.c -o build/2_1/rst.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/highlite.c -o build/2_1/highlite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/highlite.c -o build/2_1/highlite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/docgen.c -o build/2_1/docgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/docgen.c -o build/2_1/docgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ccgutils.c -o build/2_1/ccgutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ccgutils.c -o build/2_1/ccgutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/cgmeth.c -o build/2_1/cgmeth.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/cgmeth.c -o build/2_1/cgmeth.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/cgen.c -o build/2_1/cgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/cgen.c -o build/2_1/cgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ecmasgen.c -o build/2_1/ecmasgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ecmasgen.c -o build/2_1/ecmasgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/interact.c -o build/2_1/interact.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/interact.c -o build/2_1/interact.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/passaux.c -o build/2_1/passaux.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/passaux.c -o build/2_1/passaux.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/depends.c -o build/2_1/depends.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/depends.c -o build/2_1/depends.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/transf.c -o build/2_1/transf.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/transf.c -o build/2_1/transf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/main.c -o build/2_1/main.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/main.c -o build/2_1/main.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/parseopt.c -o build/2_1/parseopt.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/parseopt.c -o build/2_1/parseopt.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nim__dat.c -o build/2_1/nim__dat.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nim__dat.c -o build/2_1/nim__dat.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/parseutils.c -o build/2_1/parseutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/parseutils.c -o build/2_1/parseutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/strutils.c -o build/2_1/strutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/strutils.c -o build/2_1/strutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/os.c -o build/2_1/os.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/os.c -o build/2_1/os.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nimrod.c -o build/2_1/nimrod.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nimrod.c -o build/2_1/nimrod.o || exit 1
    echo "$LINKER $LINK_FLAGS -o bin/nimrod  \
build/2_1/system.o \
build/2_1/times.o \
build/2_1/posix.o \
build/2_1/lists.o \
build/2_1/nhashes.o \
build/2_1/nstrtabs.o \
build/2_1/options.o \
build/2_1/msgs.o \
build/2_1/nversion.o \
build/2_1/crc.o \
build/2_1/platform.o \
build/2_1/ropes.o \
build/2_1/idents.o \
build/2_1/ast.o \
build/2_1/astalgo.o \
build/2_1/condsyms.o \
build/2_1/hashes.o \
build/2_1/strtabs.o \
build/2_1/streams.o \
build/2_1/osproc.o \
build/2_1/extccomp.o \
build/2_1/wordrecg.o \
build/2_1/commands.o \
build/2_1/llstream.o \
build/2_1/lexbase.o \
build/2_1/scanner.o \
build/2_1/nimconf.o \
build/2_1/pnimsyn.o \
build/2_1/pbraces.o \
build/2_1/rnimsyn.o \
build/2_1/filters.o \
build/2_1/ptmplsyn.o \
build/2_1/syntaxes.o \
build/2_1/rodread.o \
build/2_1/trees.o \
build/2_1/types.o \
build/2_1/math.o \
build/2_1/magicsys.o \
build/2_1/bitsets.o \
build/2_1/nimsets.o \
build/2_1/passes.o \
build/2_1/treetab.o \
build/2_1/semdata.o \
build/2_1/lookups.o \
build/2_1/importer.o \
build/2_1/rodwrite.o \
build/2_1/semfold.o \
build/2_1/evals.o \
build/2_1/procfind.o \
build/2_1/pragmas.o \
build/2_1/sem.o \
build/2_1/rst.o \
build/2_1/highlite.o \
build/2_1/docgen.o \
build/2_1/ccgutils.o \
build/2_1/cgmeth.o \
build/2_1/cgen.o \
build/2_1/ecmasgen.o \
build/2_1/interact.o \
build/2_1/passaux.o \
build/2_1/depends.o \
build/2_1/transf.o \
build/2_1/main.o \
build/2_1/parseopt.o \
build/2_1/nim__dat.o \
build/2_1/parseutils.o \
build/2_1/strutils.o \
build/2_1/os.o \
build/2_1/nimrod.o"
    $LINKER $LINK_FLAGS -o bin/nimrod  \
build/2_1/system.o \
build/2_1/times.o \
build/2_1/posix.o \
build/2_1/lists.o \
build/2_1/nhashes.o \
build/2_1/nstrtabs.o \
build/2_1/options.o \
build/2_1/msgs.o \
build/2_1/nversion.o \
build/2_1/crc.o \
build/2_1/platform.o \
build/2_1/ropes.o \
build/2_1/idents.o \
build/2_1/ast.o \
build/2_1/astalgo.o \
build/2_1/condsyms.o \
build/2_1/hashes.o \
build/2_1/strtabs.o \
build/2_1/streams.o \
build/2_1/osproc.o \
build/2_1/extccomp.o \
build/2_1/wordrecg.o \
build/2_1/commands.o \
build/2_1/llstream.o \
build/2_1/lexbase.o \
build/2_1/scanner.o \
build/2_1/nimconf.o \
build/2_1/pnimsyn.o \
build/2_1/pbraces.o \
build/2_1/rnimsyn.o \
build/2_1/filters.o \
build/2_1/ptmplsyn.o \
build/2_1/syntaxes.o \
build/2_1/rodread.o \
build/2_1/trees.o \
build/2_1/types.o \
build/2_1/math.o \
build/2_1/magicsys.o \
build/2_1/bitsets.o \
build/2_1/nimsets.o \
build/2_1/passes.o \
build/2_1/treetab.o \
build/2_1/semdata.o \
build/2_1/lookups.o \
build/2_1/importer.o \
build/2_1/rodwrite.o \
build/2_1/semfold.o \
build/2_1/evals.o \
build/2_1/procfind.o \
build/2_1/pragmas.o \
build/2_1/sem.o \
build/2_1/rst.o \
build/2_1/highlite.o \
build/2_1/docgen.o \
build/2_1/ccgutils.o \
build/2_1/cgmeth.o \
build/2_1/cgen.o \
build/2_1/ecmasgen.o \
build/2_1/interact.o \
build/2_1/passaux.o \
build/2_1/depends.o \
build/2_1/transf.o \
build/2_1/main.o \
build/2_1/parseopt.o \
build/2_1/nim__dat.o \
build/2_1/parseutils.o \
build/2_1/strutils.o \
build/2_1/os.o \
build/2_1/nimrod.o || exit 1
    ;;
  amd64)
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/system.c -o build/2_2/system.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/system.c -o build/2_2/system.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/times.c -o build/2_2/times.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/times.c -o build/2_2/times.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/posix.c -o build/2_2/posix.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/posix.c -o build/2_2/posix.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/lists.c -o build/2_2/lists.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/lists.c -o build/2_2/lists.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nhashes.c -o build/2_2/nhashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nhashes.c -o build/2_2/nhashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nstrtabs.c -o build/2_2/nstrtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nstrtabs.c -o build/2_2/nstrtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/options.c -o build/2_2/options.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/options.c -o build/2_2/options.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/msgs.c -o build/2_2/msgs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/msgs.c -o build/2_2/msgs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nversion.c -o build/2_2/nversion.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nversion.c -o build/2_2/nversion.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/crc.c -o build/2_2/crc.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/crc.c -o build/2_2/crc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/platform.c -o build/2_2/platform.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/platform.c -o build/2_2/platform.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ropes.c -o build/2_2/ropes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ropes.c -o build/2_2/ropes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/idents.c -o build/2_2/idents.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/idents.c -o build/2_2/idents.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ast.c -o build/2_2/ast.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ast.c -o build/2_2/ast.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/astalgo.c -o build/2_2/astalgo.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/astalgo.c -o build/2_2/astalgo.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/condsyms.c -o build/2_2/condsyms.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/condsyms.c -o build/2_2/condsyms.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/hashes.c -o build/2_2/hashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/hashes.c -o build/2_2/hashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/strtabs.c -o build/2_2/strtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/strtabs.c -o build/2_2/strtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/streams.c -o build/2_2/streams.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/streams.c -o build/2_2/streams.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/osproc.c -o build/2_2/osproc.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/osproc.c -o build/2_2/osproc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/extccomp.c -o build/2_2/extccomp.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/extccomp.c -o build/2_2/extccomp.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/wordrecg.c -o build/2_2/wordrecg.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/wordrecg.c -o build/2_2/wordrecg.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/commands.c -o build/2_2/commands.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/commands.c -o build/2_2/commands.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/llstream.c -o build/2_2/llstream.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/llstream.c -o build/2_2/llstream.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/lexbase.c -o build/2_2/lexbase.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/lexbase.c -o build/2_2/lexbase.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/scanner.c -o build/2_2/scanner.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/scanner.c -o build/2_2/scanner.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nimconf.c -o build/2_2/nimconf.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nimconf.c -o build/2_2/nimconf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/pnimsyn.c -o build/2_2/pnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/pnimsyn.c -o build/2_2/pnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/pbraces.c -o build/2_2/pbraces.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/pbraces.c -o build/2_2/pbraces.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/rnimsyn.c -o build/2_2/rnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/rnimsyn.c -o build/2_2/rnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/filters.c -o build/2_2/filters.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/filters.c -o build/2_2/filters.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ptmplsyn.c -o build/2_2/ptmplsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ptmplsyn.c -o build/2_2/ptmplsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/syntaxes.c -o build/2_2/syntaxes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/syntaxes.c -o build/2_2/syntaxes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/rodread.c -o build/2_2/rodread.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/rodread.c -o build/2_2/rodread.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/trees.c -o build/2_2/trees.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/trees.c -o build/2_2/trees.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/types.c -o build/2_2/types.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/types.c -o build/2_2/types.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/math.c -o build/2_2/math.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/math.c -o build/2_2/math.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/magicsys.c -o build/2_2/magicsys.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/magicsys.c -o build/2_2/magicsys.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/bitsets.c -o build/2_2/bitsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/bitsets.c -o build/2_2/bitsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nimsets.c -o build/2_2/nimsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nimsets.c -o build/2_2/nimsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/passes.c -o build/2_2/passes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/passes.c -o build/2_2/passes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/treetab.c -o build/2_2/treetab.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/treetab.c -o build/2_2/treetab.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/semdata.c -o build/2_2/semdata.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/semdata.c -o build/2_2/semdata.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/lookups.c -o build/2_2/lookups.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/lookups.c -o build/2_2/lookups.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/importer.c -o build/2_2/importer.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/importer.c -o build/2_2/importer.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/rodwrite.c -o build/2_2/rodwrite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/rodwrite.c -o build/2_2/rodwrite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/semfold.c -o build/2_2/semfold.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/semfold.c -o build/2_2/semfold.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/evals.c -o build/2_2/evals.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/evals.c -o build/2_2/evals.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/procfind.c -o build/2_2/procfind.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/procfind.c -o build/2_2/procfind.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/pragmas.c -o build/2_2/pragmas.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/pragmas.c -o build/2_2/pragmas.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/sem.c -o build/2_2/sem.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/sem.c -o build/2_2/sem.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/rst.c -o build/2_2/rst.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/rst.c -o build/2_2/rst.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/highlite.c -o build/2_2/highlite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/highlite.c -o build/2_2/highlite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/docgen.c -o build/2_2/docgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/docgen.c -o build/2_2/docgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ccgutils.c -o build/2_2/ccgutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ccgutils.c -o build/2_2/ccgutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/cgmeth.c -o build/2_2/cgmeth.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/cgmeth.c -o build/2_2/cgmeth.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/cgen.c -o build/2_2/cgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/cgen.c -o build/2_2/cgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ecmasgen.c -o build/2_2/ecmasgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ecmasgen.c -o build/2_2/ecmasgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/interact.c -o build/2_2/interact.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/interact.c -o build/2_2/interact.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/passaux.c -o build/2_2/passaux.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/passaux.c -o build/2_2/passaux.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/depends.c -o build/2_2/depends.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/depends.c -o build/2_2/depends.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/transf.c -o build/2_2/transf.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/transf.c -o build/2_2/transf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/main.c -o build/2_2/main.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/main.c -o build/2_2/main.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/parseopt.c -o build/2_2/parseopt.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/parseopt.c -o build/2_2/parseopt.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nim__dat.c -o build/2_2/nim__dat.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nim__dat.c -o build/2_2/nim__dat.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/parseutils.c -o build/2_2/parseutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/parseutils.c -o build/2_2/parseutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/strutils.c -o build/2_2/strutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/strutils.c -o build/2_2/strutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/os.c -o build/2_2/os.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/os.c -o build/2_2/os.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nimrod.c -o build/2_2/nimrod.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nimrod.c -o build/2_2/nimrod.o || exit 1
    echo "$LINKER $LINK_FLAGS -o bin/nimrod  \
build/2_2/system.o \
build/2_2/times.o \
build/2_2/posix.o \
build/2_2/lists.o \
build/2_2/nhashes.o \
build/2_2/nstrtabs.o \
build/2_2/options.o \
build/2_2/msgs.o \
build/2_2/nversion.o \
build/2_2/crc.o \
build/2_2/platform.o \
build/2_2/ropes.o \
build/2_2/idents.o \
build/2_2/ast.o \
build/2_2/astalgo.o \
build/2_2/condsyms.o \
build/2_2/hashes.o \
build/2_2/strtabs.o \
build/2_2/streams.o \
build/2_2/osproc.o \
build/2_2/extccomp.o \
build/2_2/wordrecg.o \
build/2_2/commands.o \
build/2_2/llstream.o \
build/2_2/lexbase.o \
build/2_2/scanner.o \
build/2_2/nimconf.o \
build/2_2/pnimsyn.o \
build/2_2/pbraces.o \
build/2_2/rnimsyn.o \
build/2_2/filters.o \
build/2_2/ptmplsyn.o \
build/2_2/syntaxes.o \
build/2_2/rodread.o \
build/2_2/trees.o \
build/2_2/types.o \
build/2_2/math.o \
build/2_2/magicsys.o \
build/2_2/bitsets.o \
build/2_2/nimsets.o \
build/2_2/passes.o \
build/2_2/treetab.o \
build/2_2/semdata.o \
build/2_2/lookups.o \
build/2_2/importer.o \
build/2_2/rodwrite.o \
build/2_2/semfold.o \
build/2_2/evals.o \
build/2_2/procfind.o \
build/2_2/pragmas.o \
build/2_2/sem.o \
build/2_2/rst.o \
build/2_2/highlite.o \
build/2_2/docgen.o \
build/2_2/ccgutils.o \
build/2_2/cgmeth.o \
build/2_2/cgen.o \
build/2_2/ecmasgen.o \
build/2_2/interact.o \
build/2_2/passaux.o \
build/2_2/depends.o \
build/2_2/transf.o \
build/2_2/main.o \
build/2_2/parseopt.o \
build/2_2/nim__dat.o \
build/2_2/parseutils.o \
build/2_2/strutils.o \
build/2_2/os.o \
build/2_2/nimrod.o"
    $LINKER $LINK_FLAGS -o bin/nimrod  \
build/2_2/system.o \
build/2_2/times.o \
build/2_2/posix.o \
build/2_2/lists.o \
build/2_2/nhashes.o \
build/2_2/nstrtabs.o \
build/2_2/options.o \
build/2_2/msgs.o \
build/2_2/nversion.o \
build/2_2/crc.o \
build/2_2/platform.o \
build/2_2/ropes.o \
build/2_2/idents.o \
build/2_2/ast.o \
build/2_2/astalgo.o \
build/2_2/condsyms.o \
build/2_2/hashes.o \
build/2_2/strtabs.o \
build/2_2/streams.o \
build/2_2/osproc.o \
build/2_2/extccomp.o \
build/2_2/wordrecg.o \
build/2_2/commands.o \
build/2_2/llstream.o \
build/2_2/lexbase.o \
build/2_2/scanner.o \
build/2_2/nimconf.o \
build/2_2/pnimsyn.o \
build/2_2/pbraces.o \
build/2_2/rnimsyn.o \
build/2_2/filters.o \
build/2_2/ptmplsyn.o \
build/2_2/syntaxes.o \
build/2_2/rodread.o \
build/2_2/trees.o \
build/2_2/types.o \
build/2_2/math.o \
build/2_2/magicsys.o \
build/2_2/bitsets.o \
build/2_2/nimsets.o \
build/2_2/passes.o \
build/2_2/treetab.o \
build/2_2/semdata.o \
build/2_2/lookups.o \
build/2_2/importer.o \
build/2_2/rodwrite.o \
build/2_2/semfold.o \
build/2_2/evals.o \
build/2_2/procfind.o \
build/2_2/pragmas.o \
build/2_2/sem.o \
build/2_2/rst.o \
build/2_2/highlite.o \
build/2_2/docgen.o \
build/2_2/ccgutils.o \
build/2_2/cgmeth.o \
build/2_2/cgen.o \
build/2_2/ecmasgen.o \
build/2_2/interact.o \
build/2_2/passaux.o \
build/2_2/depends.o \
build/2_2/transf.o \
build/2_2/main.o \
build/2_2/parseopt.o \
build/2_2/nim__dat.o \
build/2_2/parseutils.o \
build/2_2/strutils.o \
build/2_2/os.o \
build/2_2/nimrod.o || exit 1
    ;;
  powerpc)
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/system.c -o build/2_1/system.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/system.c -o build/2_1/system.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/times.c -o build/2_1/times.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/times.c -o build/2_1/times.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/posix.c -o build/2_1/posix.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/posix.c -o build/2_1/posix.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lists.c -o build/2_1/lists.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lists.c -o build/2_1/lists.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nhashes.c -o build/2_1/nhashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nhashes.c -o build/2_1/nhashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nstrtabs.c -o build/2_1/nstrtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nstrtabs.c -o build/2_1/nstrtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/options.c -o build/2_3/options.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/options.c -o build/2_3/options.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/msgs.c -o build/2_3/msgs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/msgs.c -o build/2_3/msgs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nversion.c -o build/2_1/nversion.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nversion.c -o build/2_1/nversion.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/crc.c -o build/2_1/crc.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/crc.c -o build/2_1/crc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/platform.c -o build/2_3/platform.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/platform.c -o build/2_3/platform.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ropes.c -o build/2_1/ropes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ropes.c -o build/2_1/ropes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/idents.c -o build/2_1/idents.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/idents.c -o build/2_1/idents.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/ast.c -o build/2_3/ast.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/ast.c -o build/2_3/ast.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/astalgo.c -o build/2_1/astalgo.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/astalgo.c -o build/2_1/astalgo.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/condsyms.c -o build/2_1/condsyms.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/condsyms.c -o build/2_1/condsyms.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/hashes.c -o build/2_1/hashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/hashes.c -o build/2_1/hashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/strtabs.c -o build/2_1/strtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/strtabs.c -o build/2_1/strtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/streams.c -o build/2_1/streams.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/streams.c -o build/2_1/streams.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/osproc.c -o build/2_1/osproc.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/osproc.c -o build/2_1/osproc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/extccomp.c -o build/2_3/extccomp.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/extccomp.c -o build/2_3/extccomp.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/wordrecg.c -o build/2_1/wordrecg.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/wordrecg.c -o build/2_1/wordrecg.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/commands.c -o build/2_3/commands.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/commands.c -o build/2_3/commands.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/llstream.c -o build/2_1/llstream.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/llstream.c -o build/2_1/llstream.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lexbase.c -o build/2_1/lexbase.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lexbase.c -o build/2_1/lexbase.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/scanner.c -o build/2_1/scanner.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/scanner.c -o build/2_1/scanner.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nimconf.c -o build/2_1/nimconf.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nimconf.c -o build/2_1/nimconf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pnimsyn.c -o build/2_1/pnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pnimsyn.c -o build/2_1/pnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pbraces.c -o build/2_1/pbraces.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pbraces.c -o build/2_1/pbraces.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rnimsyn.c -o build/2_1/rnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rnimsyn.c -o build/2_1/rnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/filters.c -o build/2_1/filters.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/filters.c -o build/2_1/filters.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ptmplsyn.c -o build/2_1/ptmplsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ptmplsyn.c -o build/2_1/ptmplsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/syntaxes.c -o build/2_1/syntaxes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/syntaxes.c -o build/2_1/syntaxes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rodread.c -o build/2_1/rodread.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rodread.c -o build/2_1/rodread.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/trees.c -o build/2_1/trees.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/trees.c -o build/2_1/trees.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/types.c -o build/2_3/types.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/types.c -o build/2_3/types.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/math.c -o build/2_1/math.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/math.c -o build/2_1/math.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/magicsys.c -o build/2_1/magicsys.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/magicsys.c -o build/2_1/magicsys.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/bitsets.c -o build/2_1/bitsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/bitsets.c -o build/2_1/bitsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nimsets.c -o build/2_1/nimsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nimsets.c -o build/2_1/nimsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/passes.c -o build/2_3/passes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/passes.c -o build/2_3/passes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/treetab.c -o build/2_1/treetab.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/treetab.c -o build/2_1/treetab.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/semdata.c -o build/2_1/semdata.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/semdata.c -o build/2_1/semdata.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/lookups.c -o build/2_3/lookups.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/lookups.c -o build/2_3/lookups.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/importer.c -o build/2_3/importer.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/importer.c -o build/2_3/importer.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/rodwrite.c -o build/2_3/rodwrite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/rodwrite.c -o build/2_3/rodwrite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/semfold.c -o build/2_3/semfold.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/semfold.c -o build/2_3/semfold.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/evals.c -o build/2_3/evals.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/evals.c -o build/2_3/evals.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/procfind.c -o build/2_1/procfind.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/procfind.c -o build/2_1/procfind.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/pragmas.c -o build/2_3/pragmas.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/pragmas.c -o build/2_3/pragmas.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/sem.c -o build/2_3/sem.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/sem.c -o build/2_3/sem.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rst.c -o build/2_1/rst.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rst.c -o build/2_1/rst.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/highlite.c -o build/2_1/highlite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/highlite.c -o build/2_1/highlite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/docgen.c -o build/2_1/docgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/docgen.c -o build/2_1/docgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ccgutils.c -o build/2_1/ccgutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ccgutils.c -o build/2_1/ccgutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/cgmeth.c -o build/2_3/cgmeth.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/cgmeth.c -o build/2_3/cgmeth.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/cgen.c -o build/2_3/cgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/cgen.c -o build/2_3/cgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/ecmasgen.c -o build/2_3/ecmasgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/ecmasgen.c -o build/2_3/ecmasgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/interact.c -o build/2_1/interact.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/interact.c -o build/2_1/interact.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/passaux.c -o build/2_1/passaux.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/passaux.c -o build/2_1/passaux.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/depends.c -o build/2_1/depends.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/depends.c -o build/2_1/depends.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/transf.c -o build/2_3/transf.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/transf.c -o build/2_3/transf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/main.c -o build/2_1/main.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/main.c -o build/2_1/main.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/parseopt.c -o build/2_1/parseopt.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/parseopt.c -o build/2_1/parseopt.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nim__dat.c -o build/2_1/nim__dat.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nim__dat.c -o build/2_1/nim__dat.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/parseutils.c -o build/2_1/parseutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/parseutils.c -o build/2_1/parseutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/strutils.c -o build/2_1/strutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/strutils.c -o build/2_1/strutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/os.c -o build/2_1/os.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/os.c -o build/2_1/os.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/nimrod.c -o build/2_3/nimrod.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/nimrod.c -o build/2_3/nimrod.o || exit 1
    echo "$LINKER $LINK_FLAGS -o bin/nimrod  \
build/2_1/system.o \
build/2_1/times.o \
build/2_1/posix.o \
build/2_1/lists.o \
build/2_1/nhashes.o \
build/2_1/nstrtabs.o \
build/2_3/options.o \
build/2_3/msgs.o \
build/2_1/nversion.o \
build/2_1/crc.o \
build/2_3/platform.o \
build/2_1/ropes.o \
build/2_1/idents.o \
build/2_3/ast.o \
build/2_1/astalgo.o \
build/2_1/condsyms.o \
build/2_1/hashes.o \
build/2_1/strtabs.o \
build/2_1/streams.o \
build/2_1/osproc.o \
build/2_3/extccomp.o \
build/2_1/wordrecg.o \
build/2_3/commands.o \
build/2_1/llstream.o \
build/2_1/lexbase.o \
build/2_1/scanner.o \
build/2_1/nimconf.o \
build/2_1/pnimsyn.o \
build/2_1/pbraces.o \
build/2_1/rnimsyn.o \
build/2_1/filters.o \
build/2_1/ptmplsyn.o \
build/2_1/syntaxes.o \
build/2_1/rodread.o \
build/2_1/trees.o \
build/2_3/types.o \
build/2_1/math.o \
build/2_1/magicsys.o \
build/2_1/bitsets.o \
build/2_1/nimsets.o \
build/2_3/passes.o \
build/2_1/treetab.o \
build/2_1/semdata.o \
build/2_3/lookups.o \
build/2_3/importer.o \
build/2_3/rodwrite.o \
build/2_3/semfold.o \
build/2_3/evals.o \
build/2_1/procfind.o \
build/2_3/pragmas.o \
build/2_3/sem.o \
build/2_1/rst.o \
build/2_1/highlite.o \
build/2_1/docgen.o \
build/2_1/ccgutils.o \
build/2_3/cgmeth.o \
build/2_3/cgen.o \
build/2_3/ecmasgen.o \
build/2_1/interact.o \
build/2_1/passaux.o \
build/2_1/depends.o \
build/2_3/transf.o \
build/2_1/main.o \
build/2_1/parseopt.o \
build/2_1/nim__dat.o \
build/2_1/parseutils.o \
build/2_1/strutils.o \
build/2_1/os.o \
build/2_3/nimrod.o"
    $LINKER $LINK_FLAGS -o bin/nimrod  \
build/2_1/system.o \
build/2_1/times.o \
build/2_1/posix.o \
build/2_1/lists.o \
build/2_1/nhashes.o \
build/2_1/nstrtabs.o \
build/2_3/options.o \
build/2_3/msgs.o \
build/2_1/nversion.o \
build/2_1/crc.o \
build/2_3/platform.o \
build/2_1/ropes.o \
build/2_1/idents.o \
build/2_3/ast.o \
build/2_1/astalgo.o \
build/2_1/condsyms.o \
build/2_1/hashes.o \
build/2_1/strtabs.o \
build/2_1/streams.o \
build/2_1/osproc.o \
build/2_3/extccomp.o \
build/2_1/wordrecg.o \
build/2_3/commands.o \
build/2_1/llstream.o \
build/2_1/lexbase.o \
build/2_1/scanner.o \
build/2_1/nimconf.o \
build/2_1/pnimsyn.o \
build/2_1/pbraces.o \
build/2_1/rnimsyn.o \
build/2_1/filters.o \
build/2_1/ptmplsyn.o \
build/2_1/syntaxes.o \
build/2_1/rodread.o \
build/2_1/trees.o \
build/2_3/types.o \
build/2_1/math.o \
build/2_1/magicsys.o \
build/2_1/bitsets.o \
build/2_1/nimsets.o \
build/2_3/passes.o \
build/2_1/treetab.o \
build/2_1/semdata.o \
build/2_3/lookups.o \
build/2_3/importer.o \
build/2_3/rodwrite.o \
build/2_3/semfold.o \
build/2_3/evals.o \
build/2_1/procfind.o \
build/2_3/pragmas.o \
build/2_3/sem.o \
build/2_1/rst.o \
build/2_1/highlite.o \
build/2_1/docgen.o \
build/2_1/ccgutils.o \
build/2_3/cgmeth.o \
build/2_3/cgen.o \
build/2_3/ecmasgen.o \
build/2_1/interact.o \
build/2_1/passaux.o \
build/2_1/depends.o \
build/2_3/transf.o \
build/2_1/main.o \
build/2_1/parseopt.o \
build/2_1/nim__dat.o \
build/2_1/parseutils.o \
build/2_1/strutils.o \
build/2_1/os.o \
build/2_3/nimrod.o || exit 1
    ;;
  *)
    echo "Error: no C code generated for: [$myos: $mycpu]"
    exit 1
    ;;
  esac
  ;;
macosx) 
  case $mycpu in
  i386)
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/system.c -o build/3_1/system.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/system.c -o build/3_1/system.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/times.c -o build/3_1/times.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/times.c -o build/3_1/times.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/posix.c -o build/3_1/posix.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/posix.c -o build/3_1/posix.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lists.c -o build/2_1/lists.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lists.c -o build/2_1/lists.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nhashes.c -o build/2_1/nhashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nhashes.c -o build/2_1/nhashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nstrtabs.c -o build/2_1/nstrtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nstrtabs.c -o build/2_1/nstrtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/options.c -o build/3_1/options.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/options.c -o build/3_1/options.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/msgs.c -o build/3_1/msgs.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/msgs.c -o build/3_1/msgs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nversion.c -o build/2_1/nversion.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nversion.c -o build/2_1/nversion.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/crc.c -o build/2_1/crc.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/crc.c -o build/2_1/crc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/platform.c -o build/3_1/platform.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/platform.c -o build/3_1/platform.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ropes.c -o build/2_1/ropes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ropes.c -o build/2_1/ropes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/idents.c -o build/2_1/idents.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/idents.c -o build/2_1/idents.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ast.c -o build/2_1/ast.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ast.c -o build/2_1/ast.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/astalgo.c -o build/2_1/astalgo.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/astalgo.c -o build/2_1/astalgo.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/condsyms.c -o build/2_1/condsyms.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/condsyms.c -o build/2_1/condsyms.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/hashes.c -o build/2_1/hashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/hashes.c -o build/2_1/hashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/strtabs.c -o build/2_1/strtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/strtabs.c -o build/2_1/strtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/streams.c -o build/2_1/streams.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/streams.c -o build/2_1/streams.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/osproc.c -o build/3_1/osproc.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/osproc.c -o build/3_1/osproc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/extccomp.c -o build/3_1/extccomp.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/extccomp.c -o build/3_1/extccomp.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/wordrecg.c -o build/2_1/wordrecg.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/wordrecg.c -o build/2_1/wordrecg.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/commands.c -o build/3_1/commands.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/commands.c -o build/3_1/commands.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/llstream.c -o build/2_1/llstream.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/llstream.c -o build/2_1/llstream.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lexbase.c -o build/2_1/lexbase.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lexbase.c -o build/2_1/lexbase.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/scanner.c -o build/2_1/scanner.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/scanner.c -o build/2_1/scanner.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/nimconf.c -o build/3_1/nimconf.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/nimconf.c -o build/3_1/nimconf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pnimsyn.c -o build/2_1/pnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pnimsyn.c -o build/2_1/pnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pbraces.c -o build/2_1/pbraces.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pbraces.c -o build/2_1/pbraces.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rnimsyn.c -o build/2_1/rnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rnimsyn.c -o build/2_1/rnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/filters.c -o build/2_1/filters.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/filters.c -o build/2_1/filters.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ptmplsyn.c -o build/2_1/ptmplsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ptmplsyn.c -o build/2_1/ptmplsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/syntaxes.c -o build/3_1/syntaxes.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/syntaxes.c -o build/3_1/syntaxes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rodread.c -o build/2_1/rodread.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rodread.c -o build/2_1/rodread.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/trees.c -o build/2_1/trees.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/trees.c -o build/2_1/trees.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/types.c -o build/2_1/types.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/types.c -o build/2_1/types.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/math.c -o build/2_1/math.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/math.c -o build/2_1/math.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/magicsys.c -o build/2_1/magicsys.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/magicsys.c -o build/2_1/magicsys.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/bitsets.c -o build/2_1/bitsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/bitsets.c -o build/2_1/bitsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nimsets.c -o build/2_1/nimsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nimsets.c -o build/2_1/nimsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/passes.c -o build/2_1/passes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/passes.c -o build/2_1/passes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/treetab.c -o build/2_1/treetab.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/treetab.c -o build/2_1/treetab.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/semdata.c -o build/2_1/semdata.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/semdata.c -o build/2_1/semdata.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lookups.c -o build/2_1/lookups.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lookups.c -o build/2_1/lookups.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/importer.c -o build/2_1/importer.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/importer.c -o build/2_1/importer.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rodwrite.c -o build/2_1/rodwrite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rodwrite.c -o build/2_1/rodwrite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/semfold.c -o build/2_1/semfold.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/semfold.c -o build/2_1/semfold.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/evals.c -o build/2_1/evals.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/evals.c -o build/2_1/evals.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/procfind.c -o build/2_1/procfind.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/procfind.c -o build/2_1/procfind.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pragmas.c -o build/2_1/pragmas.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pragmas.c -o build/2_1/pragmas.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/sem.c -o build/3_1/sem.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/sem.c -o build/3_1/sem.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rst.c -o build/2_1/rst.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rst.c -o build/2_1/rst.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/highlite.c -o build/2_1/highlite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/highlite.c -o build/2_1/highlite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/docgen.c -o build/3_1/docgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/docgen.c -o build/3_1/docgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ccgutils.c -o build/2_1/ccgutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ccgutils.c -o build/2_1/ccgutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/cgmeth.c -o build/2_1/cgmeth.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/cgmeth.c -o build/2_1/cgmeth.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/cgen.c -o build/2_1/cgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/cgen.c -o build/2_1/cgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ecmasgen.c -o build/2_1/ecmasgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ecmasgen.c -o build/2_1/ecmasgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/interact.c -o build/2_1/interact.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/interact.c -o build/2_1/interact.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/passaux.c -o build/2_1/passaux.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/passaux.c -o build/2_1/passaux.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/depends.c -o build/2_1/depends.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/depends.c -o build/2_1/depends.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/transf.c -o build/2_1/transf.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/transf.c -o build/2_1/transf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/main.c -o build/2_1/main.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/main.c -o build/2_1/main.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/parseopt.c -o build/2_1/parseopt.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/parseopt.c -o build/2_1/parseopt.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nim__dat.c -o build/2_1/nim__dat.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nim__dat.c -o build/2_1/nim__dat.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/parseutils.c -o build/2_1/parseutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/parseutils.c -o build/2_1/parseutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/strutils.c -o build/2_1/strutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/strutils.c -o build/2_1/strutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/os.c -o build/3_1/os.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/os.c -o build/3_1/os.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/nimrod.c -o build/3_1/nimrod.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/nimrod.c -o build/3_1/nimrod.o || exit 1
    echo "$LINKER $LINK_FLAGS -o bin/nimrod  \
build/3_1/system.o \
build/3_1/times.o \
build/3_1/posix.o \
build/2_1/lists.o \
build/2_1/nhashes.o \
build/2_1/nstrtabs.o \
build/3_1/options.o \
build/3_1/msgs.o \
build/2_1/nversion.o \
build/2_1/crc.o \
build/3_1/platform.o \
build/2_1/ropes.o \
build/2_1/idents.o \
build/2_1/ast.o \
build/2_1/astalgo.o \
build/2_1/condsyms.o \
build/2_1/hashes.o \
build/2_1/strtabs.o \
build/2_1/streams.o \
build/3_1/osproc.o \
build/3_1/extccomp.o \
build/2_1/wordrecg.o \
build/3_1/commands.o \
build/2_1/llstream.o \
build/2_1/lexbase.o \
build/2_1/scanner.o \
build/3_1/nimconf.o \
build/2_1/pnimsyn.o \
build/2_1/pbraces.o \
build/2_1/rnimsyn.o \
build/2_1/filters.o \
build/2_1/ptmplsyn.o \
build/3_1/syntaxes.o \
build/2_1/rodread.o \
build/2_1/trees.o \
build/2_1/types.o \
build/2_1/math.o \
build/2_1/magicsys.o \
build/2_1/bitsets.o \
build/2_1/nimsets.o \
build/2_1/passes.o \
build/2_1/treetab.o \
build/2_1/semdata.o \
build/2_1/lookups.o \
build/2_1/importer.o \
build/2_1/rodwrite.o \
build/2_1/semfold.o \
build/2_1/evals.o \
build/2_1/procfind.o \
build/2_1/pragmas.o \
build/3_1/sem.o \
build/2_1/rst.o \
build/2_1/highlite.o \
build/3_1/docgen.o \
build/2_1/ccgutils.o \
build/2_1/cgmeth.o \
build/2_1/cgen.o \
build/2_1/ecmasgen.o \
build/2_1/interact.o \
build/2_1/passaux.o \
build/2_1/depends.o \
build/2_1/transf.o \
build/2_1/main.o \
build/2_1/parseopt.o \
build/2_1/nim__dat.o \
build/2_1/parseutils.o \
build/2_1/strutils.o \
build/3_1/os.o \
build/3_1/nimrod.o"
    $LINKER $LINK_FLAGS -o bin/nimrod  \
build/3_1/system.o \
build/3_1/times.o \
build/3_1/posix.o \
build/2_1/lists.o \
build/2_1/nhashes.o \
build/2_1/nstrtabs.o \
build/3_1/options.o \
build/3_1/msgs.o \
build/2_1/nversion.o \
build/2_1/crc.o \
build/3_1/platform.o \
build/2_1/ropes.o \
build/2_1/idents.o \
build/2_1/ast.o \
build/2_1/astalgo.o \
build/2_1/condsyms.o \
build/2_1/hashes.o \
build/2_1/strtabs.o \
build/2_1/streams.o \
build/3_1/osproc.o \
build/3_1/extccomp.o \
build/2_1/wordrecg.o \
build/3_1/commands.o \
build/2_1/llstream.o \
build/2_1/lexbase.o \
build/2_1/scanner.o \
build/3_1/nimconf.o \
build/2_1/pnimsyn.o \
build/2_1/pbraces.o \
build/2_1/rnimsyn.o \
build/2_1/filters.o \
build/2_1/ptmplsyn.o \
build/3_1/syntaxes.o \
build/2_1/rodread.o \
build/2_1/trees.o \
build/2_1/types.o \
build/2_1/math.o \
build/2_1/magicsys.o \
build/2_1/bitsets.o \
build/2_1/nimsets.o \
build/2_1/passes.o \
build/2_1/treetab.o \
build/2_1/semdata.o \
build/2_1/lookups.o \
build/2_1/importer.o \
build/2_1/rodwrite.o \
build/2_1/semfold.o \
build/2_1/evals.o \
build/2_1/procfind.o \
build/2_1/pragmas.o \
build/3_1/sem.o \
build/2_1/rst.o \
build/2_1/highlite.o \
build/3_1/docgen.o \
build/2_1/ccgutils.o \
build/2_1/cgmeth.o \
build/2_1/cgen.o \
build/2_1/ecmasgen.o \
build/2_1/interact.o \
build/2_1/passaux.o \
build/2_1/depends.o \
build/2_1/transf.o \
build/2_1/main.o \
build/2_1/parseopt.o \
build/2_1/nim__dat.o \
build/2_1/parseutils.o \
build/2_1/strutils.o \
build/3_1/os.o \
build/3_1/nimrod.o || exit 1
    ;;
  amd64)
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_2/system.c -o build/3_2/system.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_2/system.c -o build/3_2/system.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_2/times.c -o build/3_2/times.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_2/times.c -o build/3_2/times.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_2/posix.c -o build/3_2/posix.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_2/posix.c -o build/3_2/posix.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/lists.c -o build/2_2/lists.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/lists.c -o build/2_2/lists.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nhashes.c -o build/2_2/nhashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nhashes.c -o build/2_2/nhashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nstrtabs.c -o build/2_2/nstrtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nstrtabs.c -o build/2_2/nstrtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_2/options.c -o build/3_2/options.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_2/options.c -o build/3_2/options.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_2/msgs.c -o build/3_2/msgs.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_2/msgs.c -o build/3_2/msgs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nversion.c -o build/2_2/nversion.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nversion.c -o build/2_2/nversion.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/crc.c -o build/2_2/crc.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/crc.c -o build/2_2/crc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_2/platform.c -o build/3_2/platform.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_2/platform.c -o build/3_2/platform.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ropes.c -o build/2_2/ropes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ropes.c -o build/2_2/ropes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/idents.c -o build/2_2/idents.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/idents.c -o build/2_2/idents.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ast.c -o build/2_2/ast.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ast.c -o build/2_2/ast.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/astalgo.c -o build/2_2/astalgo.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/astalgo.c -o build/2_2/astalgo.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/condsyms.c -o build/2_2/condsyms.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/condsyms.c -o build/2_2/condsyms.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/hashes.c -o build/2_2/hashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/hashes.c -o build/2_2/hashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/strtabs.c -o build/2_2/strtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/strtabs.c -o build/2_2/strtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/streams.c -o build/2_2/streams.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/streams.c -o build/2_2/streams.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_2/osproc.c -o build/3_2/osproc.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_2/osproc.c -o build/3_2/osproc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_2/extccomp.c -o build/3_2/extccomp.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_2/extccomp.c -o build/3_2/extccomp.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/wordrecg.c -o build/2_2/wordrecg.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/wordrecg.c -o build/2_2/wordrecg.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_2/commands.c -o build/3_2/commands.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_2/commands.c -o build/3_2/commands.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/llstream.c -o build/2_2/llstream.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/llstream.c -o build/2_2/llstream.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/lexbase.c -o build/2_2/lexbase.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/lexbase.c -o build/2_2/lexbase.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/scanner.c -o build/2_2/scanner.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/scanner.c -o build/2_2/scanner.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_2/nimconf.c -o build/3_2/nimconf.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_2/nimconf.c -o build/3_2/nimconf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/pnimsyn.c -o build/2_2/pnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/pnimsyn.c -o build/2_2/pnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/pbraces.c -o build/2_2/pbraces.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/pbraces.c -o build/2_2/pbraces.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/rnimsyn.c -o build/2_2/rnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/rnimsyn.c -o build/2_2/rnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/filters.c -o build/2_2/filters.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/filters.c -o build/2_2/filters.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ptmplsyn.c -o build/2_2/ptmplsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ptmplsyn.c -o build/2_2/ptmplsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_2/syntaxes.c -o build/3_2/syntaxes.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_2/syntaxes.c -o build/3_2/syntaxes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/rodread.c -o build/2_2/rodread.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/rodread.c -o build/2_2/rodread.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/trees.c -o build/2_2/trees.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/trees.c -o build/2_2/trees.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/types.c -o build/2_2/types.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/types.c -o build/2_2/types.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/math.c -o build/2_2/math.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/math.c -o build/2_2/math.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/magicsys.c -o build/2_2/magicsys.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/magicsys.c -o build/2_2/magicsys.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/bitsets.c -o build/2_2/bitsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/bitsets.c -o build/2_2/bitsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nimsets.c -o build/2_2/nimsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nimsets.c -o build/2_2/nimsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/passes.c -o build/2_2/passes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/passes.c -o build/2_2/passes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/treetab.c -o build/2_2/treetab.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/treetab.c -o build/2_2/treetab.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/semdata.c -o build/2_2/semdata.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/semdata.c -o build/2_2/semdata.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/lookups.c -o build/2_2/lookups.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/lookups.c -o build/2_2/lookups.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/importer.c -o build/2_2/importer.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/importer.c -o build/2_2/importer.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/rodwrite.c -o build/2_2/rodwrite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/rodwrite.c -o build/2_2/rodwrite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/semfold.c -o build/2_2/semfold.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/semfold.c -o build/2_2/semfold.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/evals.c -o build/2_2/evals.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/evals.c -o build/2_2/evals.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/procfind.c -o build/2_2/procfind.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/procfind.c -o build/2_2/procfind.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/pragmas.c -o build/2_2/pragmas.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/pragmas.c -o build/2_2/pragmas.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_2/sem.c -o build/3_2/sem.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_2/sem.c -o build/3_2/sem.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/rst.c -o build/2_2/rst.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/rst.c -o build/2_2/rst.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/highlite.c -o build/2_2/highlite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/highlite.c -o build/2_2/highlite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_2/docgen.c -o build/3_2/docgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_2/docgen.c -o build/3_2/docgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ccgutils.c -o build/2_2/ccgutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ccgutils.c -o build/2_2/ccgutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/cgmeth.c -o build/2_2/cgmeth.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/cgmeth.c -o build/2_2/cgmeth.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/cgen.c -o build/2_2/cgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/cgen.c -o build/2_2/cgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ecmasgen.c -o build/2_2/ecmasgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ecmasgen.c -o build/2_2/ecmasgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/interact.c -o build/2_2/interact.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/interact.c -o build/2_2/interact.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/passaux.c -o build/2_2/passaux.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/passaux.c -o build/2_2/passaux.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/depends.c -o build/2_2/depends.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/depends.c -o build/2_2/depends.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/transf.c -o build/2_2/transf.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/transf.c -o build/2_2/transf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/main.c -o build/2_2/main.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/main.c -o build/2_2/main.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/parseopt.c -o build/2_2/parseopt.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/parseopt.c -o build/2_2/parseopt.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nim__dat.c -o build/2_2/nim__dat.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nim__dat.c -o build/2_2/nim__dat.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/parseutils.c -o build/2_2/parseutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/parseutils.c -o build/2_2/parseutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/strutils.c -o build/2_2/strutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/strutils.c -o build/2_2/strutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_2/os.c -o build/3_2/os.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_2/os.c -o build/3_2/os.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_2/nimrod.c -o build/3_2/nimrod.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_2/nimrod.c -o build/3_2/nimrod.o || exit 1
    echo "$LINKER $LINK_FLAGS -o bin/nimrod  \
build/3_2/system.o \
build/3_2/times.o \
build/3_2/posix.o \
build/2_2/lists.o \
build/2_2/nhashes.o \
build/2_2/nstrtabs.o \
build/3_2/options.o \
build/3_2/msgs.o \
build/2_2/nversion.o \
build/2_2/crc.o \
build/3_2/platform.o \
build/2_2/ropes.o \
build/2_2/idents.o \
build/2_2/ast.o \
build/2_2/astalgo.o \
build/2_2/condsyms.o \
build/2_2/hashes.o \
build/2_2/strtabs.o \
build/2_2/streams.o \
build/3_2/osproc.o \
build/3_2/extccomp.o \
build/2_2/wordrecg.o \
build/3_2/commands.o \
build/2_2/llstream.o \
build/2_2/lexbase.o \
build/2_2/scanner.o \
build/3_2/nimconf.o \
build/2_2/pnimsyn.o \
build/2_2/pbraces.o \
build/2_2/rnimsyn.o \
build/2_2/filters.o \
build/2_2/ptmplsyn.o \
build/3_2/syntaxes.o \
build/2_2/rodread.o \
build/2_2/trees.o \
build/2_2/types.o \
build/2_2/math.o \
build/2_2/magicsys.o \
build/2_2/bitsets.o \
build/2_2/nimsets.o \
build/2_2/passes.o \
build/2_2/treetab.o \
build/2_2/semdata.o \
build/2_2/lookups.o \
build/2_2/importer.o \
build/2_2/rodwrite.o \
build/2_2/semfold.o \
build/2_2/evals.o \
build/2_2/procfind.o \
build/2_2/pragmas.o \
build/3_2/sem.o \
build/2_2/rst.o \
build/2_2/highlite.o \
build/3_2/docgen.o \
build/2_2/ccgutils.o \
build/2_2/cgmeth.o \
build/2_2/cgen.o \
build/2_2/ecmasgen.o \
build/2_2/interact.o \
build/2_2/passaux.o \
build/2_2/depends.o \
build/2_2/transf.o \
build/2_2/main.o \
build/2_2/parseopt.o \
build/2_2/nim__dat.o \
build/2_2/parseutils.o \
build/2_2/strutils.o \
build/3_2/os.o \
build/3_2/nimrod.o"
    $LINKER $LINK_FLAGS -o bin/nimrod  \
build/3_2/system.o \
build/3_2/times.o \
build/3_2/posix.o \
build/2_2/lists.o \
build/2_2/nhashes.o \
build/2_2/nstrtabs.o \
build/3_2/options.o \
build/3_2/msgs.o \
build/2_2/nversion.o \
build/2_2/crc.o \
build/3_2/platform.o \
build/2_2/ropes.o \
build/2_2/idents.o \
build/2_2/ast.o \
build/2_2/astalgo.o \
build/2_2/condsyms.o \
build/2_2/hashes.o \
build/2_2/strtabs.o \
build/2_2/streams.o \
build/3_2/osproc.o \
build/3_2/extccomp.o \
build/2_2/wordrecg.o \
build/3_2/commands.o \
build/2_2/llstream.o \
build/2_2/lexbase.o \
build/2_2/scanner.o \
build/3_2/nimconf.o \
build/2_2/pnimsyn.o \
build/2_2/pbraces.o \
build/2_2/rnimsyn.o \
build/2_2/filters.o \
build/2_2/ptmplsyn.o \
build/3_2/syntaxes.o \
build/2_2/rodread.o \
build/2_2/trees.o \
build/2_2/types.o \
build/2_2/math.o \
build/2_2/magicsys.o \
build/2_2/bitsets.o \
build/2_2/nimsets.o \
build/2_2/passes.o \
build/2_2/treetab.o \
build/2_2/semdata.o \
build/2_2/lookups.o \
build/2_2/importer.o \
build/2_2/rodwrite.o \
build/2_2/semfold.o \
build/2_2/evals.o \
build/2_2/procfind.o \
build/2_2/pragmas.o \
build/3_2/sem.o \
build/2_2/rst.o \
build/2_2/highlite.o \
build/3_2/docgen.o \
build/2_2/ccgutils.o \
build/2_2/cgmeth.o \
build/2_2/cgen.o \
build/2_2/ecmasgen.o \
build/2_2/interact.o \
build/2_2/passaux.o \
build/2_2/depends.o \
build/2_2/transf.o \
build/2_2/main.o \
build/2_2/parseopt.o \
build/2_2/nim__dat.o \
build/2_2/parseutils.o \
build/2_2/strutils.o \
build/3_2/os.o \
build/3_2/nimrod.o || exit 1
    ;;
  powerpc)
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/system.c -o build/3_1/system.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/system.c -o build/3_1/system.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/times.c -o build/3_1/times.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/times.c -o build/3_1/times.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/posix.c -o build/3_1/posix.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/posix.c -o build/3_1/posix.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lists.c -o build/2_1/lists.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lists.c -o build/2_1/lists.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nhashes.c -o build/2_1/nhashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nhashes.c -o build/2_1/nhashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nstrtabs.c -o build/2_1/nstrtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nstrtabs.c -o build/2_1/nstrtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_3/options.c -o build/3_3/options.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_3/options.c -o build/3_3/options.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_3/msgs.c -o build/3_3/msgs.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_3/msgs.c -o build/3_3/msgs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nversion.c -o build/2_1/nversion.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nversion.c -o build/2_1/nversion.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/crc.c -o build/2_1/crc.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/crc.c -o build/2_1/crc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_3/platform.c -o build/3_3/platform.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_3/platform.c -o build/3_3/platform.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ropes.c -o build/2_1/ropes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ropes.c -o build/2_1/ropes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/idents.c -o build/2_1/idents.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/idents.c -o build/2_1/idents.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/ast.c -o build/2_3/ast.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/ast.c -o build/2_3/ast.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/astalgo.c -o build/2_1/astalgo.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/astalgo.c -o build/2_1/astalgo.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/condsyms.c -o build/2_1/condsyms.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/condsyms.c -o build/2_1/condsyms.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/hashes.c -o build/2_1/hashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/hashes.c -o build/2_1/hashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/strtabs.c -o build/2_1/strtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/strtabs.c -o build/2_1/strtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/streams.c -o build/2_1/streams.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/streams.c -o build/2_1/streams.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/osproc.c -o build/3_1/osproc.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/osproc.c -o build/3_1/osproc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_3/extccomp.c -o build/3_3/extccomp.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_3/extccomp.c -o build/3_3/extccomp.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/wordrecg.c -o build/2_1/wordrecg.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/wordrecg.c -o build/2_1/wordrecg.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_3/commands.c -o build/3_3/commands.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_3/commands.c -o build/3_3/commands.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/llstream.c -o build/2_1/llstream.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/llstream.c -o build/2_1/llstream.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lexbase.c -o build/2_1/lexbase.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lexbase.c -o build/2_1/lexbase.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/scanner.c -o build/2_1/scanner.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/scanner.c -o build/2_1/scanner.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/nimconf.c -o build/3_1/nimconf.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/nimconf.c -o build/3_1/nimconf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pnimsyn.c -o build/2_1/pnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pnimsyn.c -o build/2_1/pnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pbraces.c -o build/2_1/pbraces.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pbraces.c -o build/2_1/pbraces.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rnimsyn.c -o build/2_1/rnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rnimsyn.c -o build/2_1/rnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/filters.c -o build/2_1/filters.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/filters.c -o build/2_1/filters.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ptmplsyn.c -o build/2_1/ptmplsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ptmplsyn.c -o build/2_1/ptmplsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/syntaxes.c -o build/3_1/syntaxes.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/syntaxes.c -o build/3_1/syntaxes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rodread.c -o build/2_1/rodread.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rodread.c -o build/2_1/rodread.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/trees.c -o build/2_1/trees.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/trees.c -o build/2_1/trees.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/types.c -o build/2_3/types.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/types.c -o build/2_3/types.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/math.c -o build/2_1/math.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/math.c -o build/2_1/math.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/magicsys.c -o build/2_1/magicsys.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/magicsys.c -o build/2_1/magicsys.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/bitsets.c -o build/2_1/bitsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/bitsets.c -o build/2_1/bitsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nimsets.c -o build/2_1/nimsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nimsets.c -o build/2_1/nimsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/passes.c -o build/2_3/passes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/passes.c -o build/2_3/passes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/treetab.c -o build/2_1/treetab.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/treetab.c -o build/2_1/treetab.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/semdata.c -o build/2_1/semdata.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/semdata.c -o build/2_1/semdata.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/lookups.c -o build/2_3/lookups.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/lookups.c -o build/2_3/lookups.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/importer.c -o build/2_3/importer.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/importer.c -o build/2_3/importer.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/rodwrite.c -o build/2_3/rodwrite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/rodwrite.c -o build/2_3/rodwrite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/semfold.c -o build/2_3/semfold.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/semfold.c -o build/2_3/semfold.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/evals.c -o build/2_3/evals.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/evals.c -o build/2_3/evals.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/procfind.c -o build/2_1/procfind.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/procfind.c -o build/2_1/procfind.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/pragmas.c -o build/2_3/pragmas.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/pragmas.c -o build/2_3/pragmas.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_3/sem.c -o build/3_3/sem.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_3/sem.c -o build/3_3/sem.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rst.c -o build/2_1/rst.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rst.c -o build/2_1/rst.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/highlite.c -o build/2_1/highlite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/highlite.c -o build/2_1/highlite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/docgen.c -o build/3_1/docgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/docgen.c -o build/3_1/docgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ccgutils.c -o build/2_1/ccgutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ccgutils.c -o build/2_1/ccgutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/cgmeth.c -o build/2_3/cgmeth.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/cgmeth.c -o build/2_3/cgmeth.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/cgen.c -o build/2_3/cgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/cgen.c -o build/2_3/cgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/ecmasgen.c -o build/2_3/ecmasgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/ecmasgen.c -o build/2_3/ecmasgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/interact.c -o build/2_1/interact.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/interact.c -o build/2_1/interact.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/passaux.c -o build/2_1/passaux.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/passaux.c -o build/2_1/passaux.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/depends.c -o build/2_1/depends.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/depends.c -o build/2_1/depends.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/transf.c -o build/2_3/transf.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/transf.c -o build/2_3/transf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/main.c -o build/2_1/main.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/main.c -o build/2_1/main.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/parseopt.c -o build/2_1/parseopt.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/parseopt.c -o build/2_1/parseopt.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nim__dat.c -o build/2_1/nim__dat.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nim__dat.c -o build/2_1/nim__dat.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/parseutils.c -o build/2_1/parseutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/parseutils.c -o build/2_1/parseutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/strutils.c -o build/2_1/strutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/strutils.c -o build/2_1/strutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/os.c -o build/3_1/os.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/os.c -o build/3_1/os.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_3/nimrod.c -o build/3_3/nimrod.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_3/nimrod.c -o build/3_3/nimrod.o || exit 1
    echo "$LINKER $LINK_FLAGS -o bin/nimrod  \
build/3_1/system.o \
build/3_1/times.o \
build/3_1/posix.o \
build/2_1/lists.o \
build/2_1/nhashes.o \
build/2_1/nstrtabs.o \
build/3_3/options.o \
build/3_3/msgs.o \
build/2_1/nversion.o \
build/2_1/crc.o \
build/3_3/platform.o \
build/2_1/ropes.o \
build/2_1/idents.o \
build/2_3/ast.o \
build/2_1/astalgo.o \
build/2_1/condsyms.o \
build/2_1/hashes.o \
build/2_1/strtabs.o \
build/2_1/streams.o \
build/3_1/osproc.o \
build/3_3/extccomp.o \
build/2_1/wordrecg.o \
build/3_3/commands.o \
build/2_1/llstream.o \
build/2_1/lexbase.o \
build/2_1/scanner.o \
build/3_1/nimconf.o \
build/2_1/pnimsyn.o \
build/2_1/pbraces.o \
build/2_1/rnimsyn.o \
build/2_1/filters.o \
build/2_1/ptmplsyn.o \
build/3_1/syntaxes.o \
build/2_1/rodread.o \
build/2_1/trees.o \
build/2_3/types.o \
build/2_1/math.o \
build/2_1/magicsys.o \
build/2_1/bitsets.o \
build/2_1/nimsets.o \
build/2_3/passes.o \
build/2_1/treetab.o \
build/2_1/semdata.o \
build/2_3/lookups.o \
build/2_3/importer.o \
build/2_3/rodwrite.o \
build/2_3/semfold.o \
build/2_3/evals.o \
build/2_1/procfind.o \
build/2_3/pragmas.o \
build/3_3/sem.o \
build/2_1/rst.o \
build/2_1/highlite.o \
build/3_1/docgen.o \
build/2_1/ccgutils.o \
build/2_3/cgmeth.o \
build/2_3/cgen.o \
build/2_3/ecmasgen.o \
build/2_1/interact.o \
build/2_1/passaux.o \
build/2_1/depends.o \
build/2_3/transf.o \
build/2_1/main.o \
build/2_1/parseopt.o \
build/2_1/nim__dat.o \
build/2_1/parseutils.o \
build/2_1/strutils.o \
build/3_1/os.o \
build/3_3/nimrod.o"
    $LINKER $LINK_FLAGS -o bin/nimrod  \
build/3_1/system.o \
build/3_1/times.o \
build/3_1/posix.o \
build/2_1/lists.o \
build/2_1/nhashes.o \
build/2_1/nstrtabs.o \
build/3_3/options.o \
build/3_3/msgs.o \
build/2_1/nversion.o \
build/2_1/crc.o \
build/3_3/platform.o \
build/2_1/ropes.o \
build/2_1/idents.o \
build/2_3/ast.o \
build/2_1/astalgo.o \
build/2_1/condsyms.o \
build/2_1/hashes.o \
build/2_1/strtabs.o \
build/2_1/streams.o \
build/3_1/osproc.o \
build/3_3/extccomp.o \
build/2_1/wordrecg.o \
build/3_3/commands.o \
build/2_1/llstream.o \
build/2_1/lexbase.o \
build/2_1/scanner.o \
build/3_1/nimconf.o \
build/2_1/pnimsyn.o \
build/2_1/pbraces.o \
build/2_1/rnimsyn.o \
build/2_1/filters.o \
build/2_1/ptmplsyn.o \
build/3_1/syntaxes.o \
build/2_1/rodread.o \
build/2_1/trees.o \
build/2_3/types.o \
build/2_1/math.o \
build/2_1/magicsys.o \
build/2_1/bitsets.o \
build/2_1/nimsets.o \
build/2_3/passes.o \
build/2_1/treetab.o \
build/2_1/semdata.o \
build/2_3/lookups.o \
build/2_3/importer.o \
build/2_3/rodwrite.o \
build/2_3/semfold.o \
build/2_3/evals.o \
build/2_1/procfind.o \
build/2_3/pragmas.o \
build/3_3/sem.o \
build/2_1/rst.o \
build/2_1/highlite.o \
build/3_1/docgen.o \
build/2_1/ccgutils.o \
build/2_3/cgmeth.o \
build/2_3/cgen.o \
build/2_3/ecmasgen.o \
build/2_1/interact.o \
build/2_1/passaux.o \
build/2_1/depends.o \
build/2_3/transf.o \
build/2_1/main.o \
build/2_1/parseopt.o \
build/2_1/nim__dat.o \
build/2_1/parseutils.o \
build/2_1/strutils.o \
build/3_1/os.o \
build/3_3/nimrod.o || exit 1
    ;;
  *)
    echo "Error: no C code generated for: [$myos: $mycpu]"
    exit 1
    ;;
  esac
  ;;
freebsd) 
  case $mycpu in
  i386)
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/system.c -o build/4_1/system.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/system.c -o build/4_1/system.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/times.c -o build/2_1/times.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/times.c -o build/2_1/times.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/posix.c -o build/3_1/posix.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/posix.c -o build/3_1/posix.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lists.c -o build/2_1/lists.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lists.c -o build/2_1/lists.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nhashes.c -o build/2_1/nhashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nhashes.c -o build/2_1/nhashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nstrtabs.c -o build/2_1/nstrtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nstrtabs.c -o build/2_1/nstrtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/options.c -o build/4_1/options.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/options.c -o build/4_1/options.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/msgs.c -o build/4_1/msgs.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/msgs.c -o build/4_1/msgs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nversion.c -o build/2_1/nversion.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nversion.c -o build/2_1/nversion.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/crc.c -o build/2_1/crc.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/crc.c -o build/2_1/crc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/platform.c -o build/4_1/platform.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/platform.c -o build/4_1/platform.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ropes.c -o build/2_1/ropes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ropes.c -o build/2_1/ropes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/idents.c -o build/2_1/idents.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/idents.c -o build/2_1/idents.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ast.c -o build/2_1/ast.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ast.c -o build/2_1/ast.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/astalgo.c -o build/2_1/astalgo.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/astalgo.c -o build/2_1/astalgo.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/condsyms.c -o build/2_1/condsyms.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/condsyms.c -o build/2_1/condsyms.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/hashes.c -o build/2_1/hashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/hashes.c -o build/2_1/hashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/strtabs.c -o build/2_1/strtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/strtabs.c -o build/2_1/strtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/streams.c -o build/2_1/streams.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/streams.c -o build/2_1/streams.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/osproc.c -o build/3_1/osproc.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/osproc.c -o build/3_1/osproc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/extccomp.c -o build/4_1/extccomp.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/extccomp.c -o build/4_1/extccomp.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/wordrecg.c -o build/2_1/wordrecg.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/wordrecg.c -o build/2_1/wordrecg.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/commands.c -o build/4_1/commands.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/commands.c -o build/4_1/commands.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/llstream.c -o build/2_1/llstream.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/llstream.c -o build/2_1/llstream.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lexbase.c -o build/2_1/lexbase.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lexbase.c -o build/2_1/lexbase.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/scanner.c -o build/2_1/scanner.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/scanner.c -o build/2_1/scanner.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/nimconf.c -o build/4_1/nimconf.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/nimconf.c -o build/4_1/nimconf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pnimsyn.c -o build/2_1/pnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pnimsyn.c -o build/2_1/pnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pbraces.c -o build/2_1/pbraces.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pbraces.c -o build/2_1/pbraces.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rnimsyn.c -o build/2_1/rnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rnimsyn.c -o build/2_1/rnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/filters.c -o build/2_1/filters.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/filters.c -o build/2_1/filters.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ptmplsyn.c -o build/2_1/ptmplsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ptmplsyn.c -o build/2_1/ptmplsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/syntaxes.c -o build/4_1/syntaxes.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/syntaxes.c -o build/4_1/syntaxes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rodread.c -o build/2_1/rodread.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rodread.c -o build/2_1/rodread.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/trees.c -o build/2_1/trees.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/trees.c -o build/2_1/trees.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/types.c -o build/2_1/types.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/types.c -o build/2_1/types.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/math.c -o build/2_1/math.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/math.c -o build/2_1/math.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/magicsys.c -o build/2_1/magicsys.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/magicsys.c -o build/2_1/magicsys.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/bitsets.c -o build/2_1/bitsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/bitsets.c -o build/2_1/bitsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nimsets.c -o build/2_1/nimsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nimsets.c -o build/2_1/nimsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/passes.c -o build/2_1/passes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/passes.c -o build/2_1/passes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/treetab.c -o build/2_1/treetab.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/treetab.c -o build/2_1/treetab.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/semdata.c -o build/2_1/semdata.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/semdata.c -o build/2_1/semdata.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lookups.c -o build/2_1/lookups.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lookups.c -o build/2_1/lookups.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/importer.c -o build/2_1/importer.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/importer.c -o build/2_1/importer.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rodwrite.c -o build/2_1/rodwrite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rodwrite.c -o build/2_1/rodwrite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/semfold.c -o build/2_1/semfold.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/semfold.c -o build/2_1/semfold.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/evals.c -o build/2_1/evals.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/evals.c -o build/2_1/evals.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/procfind.c -o build/2_1/procfind.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/procfind.c -o build/2_1/procfind.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pragmas.c -o build/2_1/pragmas.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pragmas.c -o build/2_1/pragmas.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/sem.c -o build/4_1/sem.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/sem.c -o build/4_1/sem.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rst.c -o build/2_1/rst.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rst.c -o build/2_1/rst.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/highlite.c -o build/2_1/highlite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/highlite.c -o build/2_1/highlite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/docgen.c -o build/4_1/docgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/docgen.c -o build/4_1/docgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ccgutils.c -o build/2_1/ccgutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ccgutils.c -o build/2_1/ccgutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/cgmeth.c -o build/2_1/cgmeth.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/cgmeth.c -o build/2_1/cgmeth.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/cgen.c -o build/2_1/cgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/cgen.c -o build/2_1/cgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ecmasgen.c -o build/2_1/ecmasgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ecmasgen.c -o build/2_1/ecmasgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/interact.c -o build/2_1/interact.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/interact.c -o build/2_1/interact.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/passaux.c -o build/2_1/passaux.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/passaux.c -o build/2_1/passaux.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/depends.c -o build/2_1/depends.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/depends.c -o build/2_1/depends.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/transf.c -o build/2_1/transf.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/transf.c -o build/2_1/transf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/main.c -o build/2_1/main.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/main.c -o build/2_1/main.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/parseopt.c -o build/2_1/parseopt.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/parseopt.c -o build/2_1/parseopt.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nim__dat.c -o build/2_1/nim__dat.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nim__dat.c -o build/2_1/nim__dat.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/parseutils.c -o build/2_1/parseutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/parseutils.c -o build/2_1/parseutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/strutils.c -o build/2_1/strutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/strutils.c -o build/2_1/strutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/os.c -o build/4_1/os.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/os.c -o build/4_1/os.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/nimrod.c -o build/4_1/nimrod.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/nimrod.c -o build/4_1/nimrod.o || exit 1
    echo "$LINKER $LINK_FLAGS -o bin/nimrod  \
build/4_1/system.o \
build/2_1/times.o \
build/3_1/posix.o \
build/2_1/lists.o \
build/2_1/nhashes.o \
build/2_1/nstrtabs.o \
build/4_1/options.o \
build/4_1/msgs.o \
build/2_1/nversion.o \
build/2_1/crc.o \
build/4_1/platform.o \
build/2_1/ropes.o \
build/2_1/idents.o \
build/2_1/ast.o \
build/2_1/astalgo.o \
build/2_1/condsyms.o \
build/2_1/hashes.o \
build/2_1/strtabs.o \
build/2_1/streams.o \
build/3_1/osproc.o \
build/4_1/extccomp.o \
build/2_1/wordrecg.o \
build/4_1/commands.o \
build/2_1/llstream.o \
build/2_1/lexbase.o \
build/2_1/scanner.o \
build/4_1/nimconf.o \
build/2_1/pnimsyn.o \
build/2_1/pbraces.o \
build/2_1/rnimsyn.o \
build/2_1/filters.o \
build/2_1/ptmplsyn.o \
build/4_1/syntaxes.o \
build/2_1/rodread.o \
build/2_1/trees.o \
build/2_1/types.o \
build/2_1/math.o \
build/2_1/magicsys.o \
build/2_1/bitsets.o \
build/2_1/nimsets.o \
build/2_1/passes.o \
build/2_1/treetab.o \
build/2_1/semdata.o \
build/2_1/lookups.o \
build/2_1/importer.o \
build/2_1/rodwrite.o \
build/2_1/semfold.o \
build/2_1/evals.o \
build/2_1/procfind.o \
build/2_1/pragmas.o \
build/4_1/sem.o \
build/2_1/rst.o \
build/2_1/highlite.o \
build/4_1/docgen.o \
build/2_1/ccgutils.o \
build/2_1/cgmeth.o \
build/2_1/cgen.o \
build/2_1/ecmasgen.o \
build/2_1/interact.o \
build/2_1/passaux.o \
build/2_1/depends.o \
build/2_1/transf.o \
build/2_1/main.o \
build/2_1/parseopt.o \
build/2_1/nim__dat.o \
build/2_1/parseutils.o \
build/2_1/strutils.o \
build/4_1/os.o \
build/4_1/nimrod.o"
    $LINKER $LINK_FLAGS -o bin/nimrod  \
build/4_1/system.o \
build/2_1/times.o \
build/3_1/posix.o \
build/2_1/lists.o \
build/2_1/nhashes.o \
build/2_1/nstrtabs.o \
build/4_1/options.o \
build/4_1/msgs.o \
build/2_1/nversion.o \
build/2_1/crc.o \
build/4_1/platform.o \
build/2_1/ropes.o \
build/2_1/idents.o \
build/2_1/ast.o \
build/2_1/astalgo.o \
build/2_1/condsyms.o \
build/2_1/hashes.o \
build/2_1/strtabs.o \
build/2_1/streams.o \
build/3_1/osproc.o \
build/4_1/extccomp.o \
build/2_1/wordrecg.o \
build/4_1/commands.o \
build/2_1/llstream.o \
build/2_1/lexbase.o \
build/2_1/scanner.o \
build/4_1/nimconf.o \
build/2_1/pnimsyn.o \
build/2_1/pbraces.o \
build/2_1/rnimsyn.o \
build/2_1/filters.o \
build/2_1/ptmplsyn.o \
build/4_1/syntaxes.o \
build/2_1/rodread.o \
build/2_1/trees.o \
build/2_1/types.o \
build/2_1/math.o \
build/2_1/magicsys.o \
build/2_1/bitsets.o \
build/2_1/nimsets.o \
build/2_1/passes.o \
build/2_1/treetab.o \
build/2_1/semdata.o \
build/2_1/lookups.o \
build/2_1/importer.o \
build/2_1/rodwrite.o \
build/2_1/semfold.o \
build/2_1/evals.o \
build/2_1/procfind.o \
build/2_1/pragmas.o \
build/4_1/sem.o \
build/2_1/rst.o \
build/2_1/highlite.o \
build/4_1/docgen.o \
build/2_1/ccgutils.o \
build/2_1/cgmeth.o \
build/2_1/cgen.o \
build/2_1/ecmasgen.o \
build/2_1/interact.o \
build/2_1/passaux.o \
build/2_1/depends.o \
build/2_1/transf.o \
build/2_1/main.o \
build/2_1/parseopt.o \
build/2_1/nim__dat.o \
build/2_1/parseutils.o \
build/2_1/strutils.o \
build/4_1/os.o \
build/4_1/nimrod.o || exit 1
    ;;
  amd64)
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/system.c -o build/4_2/system.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/system.c -o build/4_2/system.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/times.c -o build/2_2/times.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/times.c -o build/2_2/times.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_2/posix.c -o build/3_2/posix.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_2/posix.c -o build/3_2/posix.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/lists.c -o build/2_2/lists.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/lists.c -o build/2_2/lists.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nhashes.c -o build/2_2/nhashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nhashes.c -o build/2_2/nhashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nstrtabs.c -o build/2_2/nstrtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nstrtabs.c -o build/2_2/nstrtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/options.c -o build/4_2/options.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/options.c -o build/4_2/options.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/msgs.c -o build/4_2/msgs.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/msgs.c -o build/4_2/msgs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nversion.c -o build/2_2/nversion.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nversion.c -o build/2_2/nversion.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/crc.c -o build/2_2/crc.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/crc.c -o build/2_2/crc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/platform.c -o build/4_2/platform.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/platform.c -o build/4_2/platform.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ropes.c -o build/2_2/ropes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ropes.c -o build/2_2/ropes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/idents.c -o build/2_2/idents.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/idents.c -o build/2_2/idents.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ast.c -o build/2_2/ast.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ast.c -o build/2_2/ast.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/astalgo.c -o build/2_2/astalgo.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/astalgo.c -o build/2_2/astalgo.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/condsyms.c -o build/2_2/condsyms.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/condsyms.c -o build/2_2/condsyms.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/hashes.c -o build/2_2/hashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/hashes.c -o build/2_2/hashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/strtabs.c -o build/2_2/strtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/strtabs.c -o build/2_2/strtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/streams.c -o build/2_2/streams.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/streams.c -o build/2_2/streams.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_2/osproc.c -o build/3_2/osproc.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_2/osproc.c -o build/3_2/osproc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/extccomp.c -o build/4_2/extccomp.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/extccomp.c -o build/4_2/extccomp.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/wordrecg.c -o build/2_2/wordrecg.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/wordrecg.c -o build/2_2/wordrecg.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/commands.c -o build/4_2/commands.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/commands.c -o build/4_2/commands.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/llstream.c -o build/2_2/llstream.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/llstream.c -o build/2_2/llstream.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/lexbase.c -o build/2_2/lexbase.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/lexbase.c -o build/2_2/lexbase.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/scanner.c -o build/2_2/scanner.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/scanner.c -o build/2_2/scanner.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/nimconf.c -o build/4_2/nimconf.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/nimconf.c -o build/4_2/nimconf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/pnimsyn.c -o build/2_2/pnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/pnimsyn.c -o build/2_2/pnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/pbraces.c -o build/2_2/pbraces.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/pbraces.c -o build/2_2/pbraces.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/rnimsyn.c -o build/2_2/rnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/rnimsyn.c -o build/2_2/rnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/filters.c -o build/2_2/filters.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/filters.c -o build/2_2/filters.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ptmplsyn.c -o build/2_2/ptmplsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ptmplsyn.c -o build/2_2/ptmplsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/syntaxes.c -o build/4_2/syntaxes.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/syntaxes.c -o build/4_2/syntaxes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/rodread.c -o build/2_2/rodread.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/rodread.c -o build/2_2/rodread.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/trees.c -o build/2_2/trees.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/trees.c -o build/2_2/trees.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/types.c -o build/2_2/types.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/types.c -o build/2_2/types.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/math.c -o build/2_2/math.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/math.c -o build/2_2/math.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/magicsys.c -o build/2_2/magicsys.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/magicsys.c -o build/2_2/magicsys.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/bitsets.c -o build/2_2/bitsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/bitsets.c -o build/2_2/bitsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nimsets.c -o build/2_2/nimsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nimsets.c -o build/2_2/nimsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/passes.c -o build/2_2/passes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/passes.c -o build/2_2/passes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/treetab.c -o build/2_2/treetab.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/treetab.c -o build/2_2/treetab.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/semdata.c -o build/2_2/semdata.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/semdata.c -o build/2_2/semdata.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/lookups.c -o build/2_2/lookups.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/lookups.c -o build/2_2/lookups.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/importer.c -o build/2_2/importer.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/importer.c -o build/2_2/importer.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/rodwrite.c -o build/2_2/rodwrite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/rodwrite.c -o build/2_2/rodwrite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/semfold.c -o build/2_2/semfold.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/semfold.c -o build/2_2/semfold.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/evals.c -o build/2_2/evals.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/evals.c -o build/2_2/evals.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/procfind.c -o build/2_2/procfind.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/procfind.c -o build/2_2/procfind.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/pragmas.c -o build/2_2/pragmas.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/pragmas.c -o build/2_2/pragmas.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/sem.c -o build/4_2/sem.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/sem.c -o build/4_2/sem.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/rst.c -o build/2_2/rst.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/rst.c -o build/2_2/rst.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/highlite.c -o build/2_2/highlite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/highlite.c -o build/2_2/highlite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/docgen.c -o build/4_2/docgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/docgen.c -o build/4_2/docgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ccgutils.c -o build/2_2/ccgutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ccgutils.c -o build/2_2/ccgutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/cgmeth.c -o build/2_2/cgmeth.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/cgmeth.c -o build/2_2/cgmeth.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/cgen.c -o build/2_2/cgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/cgen.c -o build/2_2/cgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ecmasgen.c -o build/2_2/ecmasgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ecmasgen.c -o build/2_2/ecmasgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/interact.c -o build/2_2/interact.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/interact.c -o build/2_2/interact.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/passaux.c -o build/2_2/passaux.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/passaux.c -o build/2_2/passaux.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/depends.c -o build/2_2/depends.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/depends.c -o build/2_2/depends.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/transf.c -o build/2_2/transf.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/transf.c -o build/2_2/transf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/main.c -o build/2_2/main.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/main.c -o build/2_2/main.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/parseopt.c -o build/2_2/parseopt.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/parseopt.c -o build/2_2/parseopt.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nim__dat.c -o build/2_2/nim__dat.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nim__dat.c -o build/2_2/nim__dat.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/parseutils.c -o build/2_2/parseutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/parseutils.c -o build/2_2/parseutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/strutils.c -o build/2_2/strutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/strutils.c -o build/2_2/strutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/os.c -o build/4_2/os.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/os.c -o build/4_2/os.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/nimrod.c -o build/4_2/nimrod.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/nimrod.c -o build/4_2/nimrod.o || exit 1
    echo "$LINKER $LINK_FLAGS -o bin/nimrod  \
build/4_2/system.o \
build/2_2/times.o \
build/3_2/posix.o \
build/2_2/lists.o \
build/2_2/nhashes.o \
build/2_2/nstrtabs.o \
build/4_2/options.o \
build/4_2/msgs.o \
build/2_2/nversion.o \
build/2_2/crc.o \
build/4_2/platform.o \
build/2_2/ropes.o \
build/2_2/idents.o \
build/2_2/ast.o \
build/2_2/astalgo.o \
build/2_2/condsyms.o \
build/2_2/hashes.o \
build/2_2/strtabs.o \
build/2_2/streams.o \
build/3_2/osproc.o \
build/4_2/extccomp.o \
build/2_2/wordrecg.o \
build/4_2/commands.o \
build/2_2/llstream.o \
build/2_2/lexbase.o \
build/2_2/scanner.o \
build/4_2/nimconf.o \
build/2_2/pnimsyn.o \
build/2_2/pbraces.o \
build/2_2/rnimsyn.o \
build/2_2/filters.o \
build/2_2/ptmplsyn.o \
build/4_2/syntaxes.o \
build/2_2/rodread.o \
build/2_2/trees.o \
build/2_2/types.o \
build/2_2/math.o \
build/2_2/magicsys.o \
build/2_2/bitsets.o \
build/2_2/nimsets.o \
build/2_2/passes.o \
build/2_2/treetab.o \
build/2_2/semdata.o \
build/2_2/lookups.o \
build/2_2/importer.o \
build/2_2/rodwrite.o \
build/2_2/semfold.o \
build/2_2/evals.o \
build/2_2/procfind.o \
build/2_2/pragmas.o \
build/4_2/sem.o \
build/2_2/rst.o \
build/2_2/highlite.o \
build/4_2/docgen.o \
build/2_2/ccgutils.o \
build/2_2/cgmeth.o \
build/2_2/cgen.o \
build/2_2/ecmasgen.o \
build/2_2/interact.o \
build/2_2/passaux.o \
build/2_2/depends.o \
build/2_2/transf.o \
build/2_2/main.o \
build/2_2/parseopt.o \
build/2_2/nim__dat.o \
build/2_2/parseutils.o \
build/2_2/strutils.o \
build/4_2/os.o \
build/4_2/nimrod.o"
    $LINKER $LINK_FLAGS -o bin/nimrod  \
build/4_2/system.o \
build/2_2/times.o \
build/3_2/posix.o \
build/2_2/lists.o \
build/2_2/nhashes.o \
build/2_2/nstrtabs.o \
build/4_2/options.o \
build/4_2/msgs.o \
build/2_2/nversion.o \
build/2_2/crc.o \
build/4_2/platform.o \
build/2_2/ropes.o \
build/2_2/idents.o \
build/2_2/ast.o \
build/2_2/astalgo.o \
build/2_2/condsyms.o \
build/2_2/hashes.o \
build/2_2/strtabs.o \
build/2_2/streams.o \
build/3_2/osproc.o \
build/4_2/extccomp.o \
build/2_2/wordrecg.o \
build/4_2/commands.o \
build/2_2/llstream.o \
build/2_2/lexbase.o \
build/2_2/scanner.o \
build/4_2/nimconf.o \
build/2_2/pnimsyn.o \
build/2_2/pbraces.o \
build/2_2/rnimsyn.o \
build/2_2/filters.o \
build/2_2/ptmplsyn.o \
build/4_2/syntaxes.o \
build/2_2/rodread.o \
build/2_2/trees.o \
build/2_2/types.o \
build/2_2/math.o \
build/2_2/magicsys.o \
build/2_2/bitsets.o \
build/2_2/nimsets.o \
build/2_2/passes.o \
build/2_2/treetab.o \
build/2_2/semdata.o \
build/2_2/lookups.o \
build/2_2/importer.o \
build/2_2/rodwrite.o \
build/2_2/semfold.o \
build/2_2/evals.o \
build/2_2/procfind.o \
build/2_2/pragmas.o \
build/4_2/sem.o \
build/2_2/rst.o \
build/2_2/highlite.o \
build/4_2/docgen.o \
build/2_2/ccgutils.o \
build/2_2/cgmeth.o \
build/2_2/cgen.o \
build/2_2/ecmasgen.o \
build/2_2/interact.o \
build/2_2/passaux.o \
build/2_2/depends.o \
build/2_2/transf.o \
build/2_2/main.o \
build/2_2/parseopt.o \
build/2_2/nim__dat.o \
build/2_2/parseutils.o \
build/2_2/strutils.o \
build/4_2/os.o \
build/4_2/nimrod.o || exit 1
    ;;
  powerpc)
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/system.c -o build/4_1/system.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/system.c -o build/4_1/system.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/times.c -o build/2_1/times.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/times.c -o build/2_1/times.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/posix.c -o build/3_1/posix.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/posix.c -o build/3_1/posix.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lists.c -o build/2_1/lists.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lists.c -o build/2_1/lists.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nhashes.c -o build/2_1/nhashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nhashes.c -o build/2_1/nhashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nstrtabs.c -o build/2_1/nstrtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nstrtabs.c -o build/2_1/nstrtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/options.c -o build/4_3/options.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/options.c -o build/4_3/options.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/msgs.c -o build/4_3/msgs.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/msgs.c -o build/4_3/msgs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nversion.c -o build/2_1/nversion.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nversion.c -o build/2_1/nversion.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/crc.c -o build/2_1/crc.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/crc.c -o build/2_1/crc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/platform.c -o build/4_3/platform.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/platform.c -o build/4_3/platform.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ropes.c -o build/2_1/ropes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ropes.c -o build/2_1/ropes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/idents.c -o build/2_1/idents.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/idents.c -o build/2_1/idents.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/ast.c -o build/2_3/ast.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/ast.c -o build/2_3/ast.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/astalgo.c -o build/2_1/astalgo.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/astalgo.c -o build/2_1/astalgo.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/condsyms.c -o build/2_1/condsyms.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/condsyms.c -o build/2_1/condsyms.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/hashes.c -o build/2_1/hashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/hashes.c -o build/2_1/hashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/strtabs.c -o build/2_1/strtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/strtabs.c -o build/2_1/strtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/streams.c -o build/2_1/streams.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/streams.c -o build/2_1/streams.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/osproc.c -o build/3_1/osproc.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/osproc.c -o build/3_1/osproc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/extccomp.c -o build/4_3/extccomp.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/extccomp.c -o build/4_3/extccomp.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/wordrecg.c -o build/2_1/wordrecg.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/wordrecg.c -o build/2_1/wordrecg.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/commands.c -o build/4_3/commands.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/commands.c -o build/4_3/commands.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/llstream.c -o build/2_1/llstream.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/llstream.c -o build/2_1/llstream.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lexbase.c -o build/2_1/lexbase.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lexbase.c -o build/2_1/lexbase.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/scanner.c -o build/2_1/scanner.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/scanner.c -o build/2_1/scanner.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/nimconf.c -o build/4_1/nimconf.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/nimconf.c -o build/4_1/nimconf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pnimsyn.c -o build/2_1/pnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pnimsyn.c -o build/2_1/pnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pbraces.c -o build/2_1/pbraces.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pbraces.c -o build/2_1/pbraces.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rnimsyn.c -o build/2_1/rnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rnimsyn.c -o build/2_1/rnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/filters.c -o build/2_1/filters.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/filters.c -o build/2_1/filters.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ptmplsyn.c -o build/2_1/ptmplsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ptmplsyn.c -o build/2_1/ptmplsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/syntaxes.c -o build/4_1/syntaxes.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/syntaxes.c -o build/4_1/syntaxes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rodread.c -o build/2_1/rodread.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rodread.c -o build/2_1/rodread.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/trees.c -o build/2_1/trees.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/trees.c -o build/2_1/trees.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/types.c -o build/2_3/types.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/types.c -o build/2_3/types.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/math.c -o build/2_1/math.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/math.c -o build/2_1/math.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/magicsys.c -o build/2_1/magicsys.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/magicsys.c -o build/2_1/magicsys.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/bitsets.c -o build/2_1/bitsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/bitsets.c -o build/2_1/bitsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nimsets.c -o build/2_1/nimsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nimsets.c -o build/2_1/nimsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/passes.c -o build/2_3/passes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/passes.c -o build/2_3/passes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/treetab.c -o build/2_1/treetab.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/treetab.c -o build/2_1/treetab.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/semdata.c -o build/2_1/semdata.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/semdata.c -o build/2_1/semdata.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/lookups.c -o build/2_3/lookups.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/lookups.c -o build/2_3/lookups.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/importer.c -o build/2_3/importer.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/importer.c -o build/2_3/importer.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/rodwrite.c -o build/2_3/rodwrite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/rodwrite.c -o build/2_3/rodwrite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/semfold.c -o build/2_3/semfold.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/semfold.c -o build/2_3/semfold.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/evals.c -o build/2_3/evals.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/evals.c -o build/2_3/evals.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/procfind.c -o build/2_1/procfind.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/procfind.c -o build/2_1/procfind.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/pragmas.c -o build/2_3/pragmas.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/pragmas.c -o build/2_3/pragmas.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/sem.c -o build/4_3/sem.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/sem.c -o build/4_3/sem.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rst.c -o build/2_1/rst.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rst.c -o build/2_1/rst.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/highlite.c -o build/2_1/highlite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/highlite.c -o build/2_1/highlite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/docgen.c -o build/4_1/docgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/docgen.c -o build/4_1/docgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ccgutils.c -o build/2_1/ccgutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ccgutils.c -o build/2_1/ccgutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/cgmeth.c -o build/2_3/cgmeth.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/cgmeth.c -o build/2_3/cgmeth.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/cgen.c -o build/2_3/cgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/cgen.c -o build/2_3/cgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/ecmasgen.c -o build/2_3/ecmasgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/ecmasgen.c -o build/2_3/ecmasgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/interact.c -o build/2_1/interact.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/interact.c -o build/2_1/interact.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/passaux.c -o build/2_1/passaux.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/passaux.c -o build/2_1/passaux.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/depends.c -o build/2_1/depends.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/depends.c -o build/2_1/depends.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/transf.c -o build/2_3/transf.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/transf.c -o build/2_3/transf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/main.c -o build/2_1/main.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/main.c -o build/2_1/main.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/parseopt.c -o build/2_1/parseopt.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/parseopt.c -o build/2_1/parseopt.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nim__dat.c -o build/2_1/nim__dat.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nim__dat.c -o build/2_1/nim__dat.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/parseutils.c -o build/2_1/parseutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/parseutils.c -o build/2_1/parseutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/strutils.c -o build/2_1/strutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/strutils.c -o build/2_1/strutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/os.c -o build/4_1/os.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/os.c -o build/4_1/os.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/nimrod.c -o build/4_3/nimrod.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/nimrod.c -o build/4_3/nimrod.o || exit 1
    echo "$LINKER $LINK_FLAGS -o bin/nimrod  \
build/4_1/system.o \
build/2_1/times.o \
build/3_1/posix.o \
build/2_1/lists.o \
build/2_1/nhashes.o \
build/2_1/nstrtabs.o \
build/4_3/options.o \
build/4_3/msgs.o \
build/2_1/nversion.o \
build/2_1/crc.o \
build/4_3/platform.o \
build/2_1/ropes.o \
build/2_1/idents.o \
build/2_3/ast.o \
build/2_1/astalgo.o \
build/2_1/condsyms.o \
build/2_1/hashes.o \
build/2_1/strtabs.o \
build/2_1/streams.o \
build/3_1/osproc.o \
build/4_3/extccomp.o \
build/2_1/wordrecg.o \
build/4_3/commands.o \
build/2_1/llstream.o \
build/2_1/lexbase.o \
build/2_1/scanner.o \
build/4_1/nimconf.o \
build/2_1/pnimsyn.o \
build/2_1/pbraces.o \
build/2_1/rnimsyn.o \
build/2_1/filters.o \
build/2_1/ptmplsyn.o \
build/4_1/syntaxes.o \
build/2_1/rodread.o \
build/2_1/trees.o \
build/2_3/types.o \
build/2_1/math.o \
build/2_1/magicsys.o \
build/2_1/bitsets.o \
build/2_1/nimsets.o \
build/2_3/passes.o \
build/2_1/treetab.o \
build/2_1/semdata.o \
build/2_3/lookups.o \
build/2_3/importer.o \
build/2_3/rodwrite.o \
build/2_3/semfold.o \
build/2_3/evals.o \
build/2_1/procfind.o \
build/2_3/pragmas.o \
build/4_3/sem.o \
build/2_1/rst.o \
build/2_1/highlite.o \
build/4_1/docgen.o \
build/2_1/ccgutils.o \
build/2_3/cgmeth.o \
build/2_3/cgen.o \
build/2_3/ecmasgen.o \
build/2_1/interact.o \
build/2_1/passaux.o \
build/2_1/depends.o \
build/2_3/transf.o \
build/2_1/main.o \
build/2_1/parseopt.o \
build/2_1/nim__dat.o \
build/2_1/parseutils.o \
build/2_1/strutils.o \
build/4_1/os.o \
build/4_3/nimrod.o"
    $LINKER $LINK_FLAGS -o bin/nimrod  \
build/4_1/system.o \
build/2_1/times.o \
build/3_1/posix.o \
build/2_1/lists.o \
build/2_1/nhashes.o \
build/2_1/nstrtabs.o \
build/4_3/options.o \
build/4_3/msgs.o \
build/2_1/nversion.o \
build/2_1/crc.o \
build/4_3/platform.o \
build/2_1/ropes.o \
build/2_1/idents.o \
build/2_3/ast.o \
build/2_1/astalgo.o \
build/2_1/condsyms.o \
build/2_1/hashes.o \
build/2_1/strtabs.o \
build/2_1/streams.o \
build/3_1/osproc.o \
build/4_3/extccomp.o \
build/2_1/wordrecg.o \
build/4_3/commands.o \
build/2_1/llstream.o \
build/2_1/lexbase.o \
build/2_1/scanner.o \
build/4_1/nimconf.o \
build/2_1/pnimsyn.o \
build/2_1/pbraces.o \
build/2_1/rnimsyn.o \
build/2_1/filters.o \
build/2_1/ptmplsyn.o \
build/4_1/syntaxes.o \
build/2_1/rodread.o \
build/2_1/trees.o \
build/2_3/types.o \
build/2_1/math.o \
build/2_1/magicsys.o \
build/2_1/bitsets.o \
build/2_1/nimsets.o \
build/2_3/passes.o \
build/2_1/treetab.o \
build/2_1/semdata.o \
build/2_3/lookups.o \
build/2_3/importer.o \
build/2_3/rodwrite.o \
build/2_3/semfold.o \
build/2_3/evals.o \
build/2_1/procfind.o \
build/2_3/pragmas.o \
build/4_3/sem.o \
build/2_1/rst.o \
build/2_1/highlite.o \
build/4_1/docgen.o \
build/2_1/ccgutils.o \
build/2_3/cgmeth.o \
build/2_3/cgen.o \
build/2_3/ecmasgen.o \
build/2_1/interact.o \
build/2_1/passaux.o \
build/2_1/depends.o \
build/2_3/transf.o \
build/2_1/main.o \
build/2_1/parseopt.o \
build/2_1/nim__dat.o \
build/2_1/parseutils.o \
build/2_1/strutils.o \
build/4_1/os.o \
build/4_3/nimrod.o || exit 1
    ;;
  *)
    echo "Error: no C code generated for: [$myos: $mycpu]"
    exit 1
    ;;
  esac
  ;;
netbsd) 
  case $mycpu in
  i386)
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/system.c -o build/4_1/system.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/system.c -o build/4_1/system.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/times.c -o build/2_1/times.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/times.c -o build/2_1/times.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/posix.c -o build/3_1/posix.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/posix.c -o build/3_1/posix.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lists.c -o build/2_1/lists.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lists.c -o build/2_1/lists.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nhashes.c -o build/2_1/nhashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nhashes.c -o build/2_1/nhashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nstrtabs.c -o build/2_1/nstrtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nstrtabs.c -o build/2_1/nstrtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/options.c -o build/4_1/options.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/options.c -o build/4_1/options.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/msgs.c -o build/4_1/msgs.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/msgs.c -o build/4_1/msgs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nversion.c -o build/2_1/nversion.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nversion.c -o build/2_1/nversion.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/crc.c -o build/2_1/crc.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/crc.c -o build/2_1/crc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/5_1/platform.c -o build/5_1/platform.o"
    $CC $COMP_FLAGS -Ibuild -c build/5_1/platform.c -o build/5_1/platform.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ropes.c -o build/2_1/ropes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ropes.c -o build/2_1/ropes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/idents.c -o build/2_1/idents.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/idents.c -o build/2_1/idents.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ast.c -o build/2_1/ast.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ast.c -o build/2_1/ast.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/astalgo.c -o build/2_1/astalgo.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/astalgo.c -o build/2_1/astalgo.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/condsyms.c -o build/2_1/condsyms.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/condsyms.c -o build/2_1/condsyms.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/hashes.c -o build/2_1/hashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/hashes.c -o build/2_1/hashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/strtabs.c -o build/2_1/strtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/strtabs.c -o build/2_1/strtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/streams.c -o build/2_1/streams.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/streams.c -o build/2_1/streams.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/osproc.c -o build/3_1/osproc.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/osproc.c -o build/3_1/osproc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/extccomp.c -o build/4_1/extccomp.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/extccomp.c -o build/4_1/extccomp.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/wordrecg.c -o build/2_1/wordrecg.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/wordrecg.c -o build/2_1/wordrecg.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/commands.c -o build/4_1/commands.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/commands.c -o build/4_1/commands.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/llstream.c -o build/2_1/llstream.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/llstream.c -o build/2_1/llstream.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lexbase.c -o build/2_1/lexbase.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lexbase.c -o build/2_1/lexbase.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/scanner.c -o build/2_1/scanner.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/scanner.c -o build/2_1/scanner.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/nimconf.c -o build/4_1/nimconf.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/nimconf.c -o build/4_1/nimconf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pnimsyn.c -o build/2_1/pnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pnimsyn.c -o build/2_1/pnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pbraces.c -o build/2_1/pbraces.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pbraces.c -o build/2_1/pbraces.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rnimsyn.c -o build/2_1/rnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rnimsyn.c -o build/2_1/rnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/filters.c -o build/2_1/filters.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/filters.c -o build/2_1/filters.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ptmplsyn.c -o build/2_1/ptmplsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ptmplsyn.c -o build/2_1/ptmplsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/syntaxes.c -o build/4_1/syntaxes.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/syntaxes.c -o build/4_1/syntaxes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rodread.c -o build/2_1/rodread.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rodread.c -o build/2_1/rodread.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/trees.c -o build/2_1/trees.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/trees.c -o build/2_1/trees.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/types.c -o build/2_1/types.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/types.c -o build/2_1/types.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/math.c -o build/2_1/math.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/math.c -o build/2_1/math.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/magicsys.c -o build/2_1/magicsys.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/magicsys.c -o build/2_1/magicsys.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/bitsets.c -o build/2_1/bitsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/bitsets.c -o build/2_1/bitsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nimsets.c -o build/2_1/nimsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nimsets.c -o build/2_1/nimsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/passes.c -o build/2_1/passes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/passes.c -o build/2_1/passes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/treetab.c -o build/2_1/treetab.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/treetab.c -o build/2_1/treetab.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/semdata.c -o build/2_1/semdata.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/semdata.c -o build/2_1/semdata.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lookups.c -o build/2_1/lookups.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lookups.c -o build/2_1/lookups.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/importer.c -o build/2_1/importer.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/importer.c -o build/2_1/importer.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rodwrite.c -o build/2_1/rodwrite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rodwrite.c -o build/2_1/rodwrite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/semfold.c -o build/2_1/semfold.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/semfold.c -o build/2_1/semfold.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/evals.c -o build/2_1/evals.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/evals.c -o build/2_1/evals.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/procfind.c -o build/2_1/procfind.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/procfind.c -o build/2_1/procfind.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pragmas.c -o build/2_1/pragmas.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pragmas.c -o build/2_1/pragmas.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/sem.c -o build/4_1/sem.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/sem.c -o build/4_1/sem.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rst.c -o build/2_1/rst.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rst.c -o build/2_1/rst.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/highlite.c -o build/2_1/highlite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/highlite.c -o build/2_1/highlite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/docgen.c -o build/4_1/docgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/docgen.c -o build/4_1/docgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ccgutils.c -o build/2_1/ccgutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ccgutils.c -o build/2_1/ccgutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/cgmeth.c -o build/2_1/cgmeth.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/cgmeth.c -o build/2_1/cgmeth.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/cgen.c -o build/2_1/cgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/cgen.c -o build/2_1/cgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ecmasgen.c -o build/2_1/ecmasgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ecmasgen.c -o build/2_1/ecmasgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/interact.c -o build/2_1/interact.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/interact.c -o build/2_1/interact.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/passaux.c -o build/2_1/passaux.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/passaux.c -o build/2_1/passaux.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/depends.c -o build/2_1/depends.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/depends.c -o build/2_1/depends.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/transf.c -o build/2_1/transf.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/transf.c -o build/2_1/transf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/main.c -o build/2_1/main.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/main.c -o build/2_1/main.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/parseopt.c -o build/2_1/parseopt.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/parseopt.c -o build/2_1/parseopt.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nim__dat.c -o build/2_1/nim__dat.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nim__dat.c -o build/2_1/nim__dat.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/parseutils.c -o build/2_1/parseutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/parseutils.c -o build/2_1/parseutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/strutils.c -o build/2_1/strutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/strutils.c -o build/2_1/strutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/os.c -o build/4_1/os.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/os.c -o build/4_1/os.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/nimrod.c -o build/4_1/nimrod.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/nimrod.c -o build/4_1/nimrod.o || exit 1
    echo "$LINKER $LINK_FLAGS -o bin/nimrod  \
build/4_1/system.o \
build/2_1/times.o \
build/3_1/posix.o \
build/2_1/lists.o \
build/2_1/nhashes.o \
build/2_1/nstrtabs.o \
build/4_1/options.o \
build/4_1/msgs.o \
build/2_1/nversion.o \
build/2_1/crc.o \
build/5_1/platform.o \
build/2_1/ropes.o \
build/2_1/idents.o \
build/2_1/ast.o \
build/2_1/astalgo.o \
build/2_1/condsyms.o \
build/2_1/hashes.o \
build/2_1/strtabs.o \
build/2_1/streams.o \
build/3_1/osproc.o \
build/4_1/extccomp.o \
build/2_1/wordrecg.o \
build/4_1/commands.o \
build/2_1/llstream.o \
build/2_1/lexbase.o \
build/2_1/scanner.o \
build/4_1/nimconf.o \
build/2_1/pnimsyn.o \
build/2_1/pbraces.o \
build/2_1/rnimsyn.o \
build/2_1/filters.o \
build/2_1/ptmplsyn.o \
build/4_1/syntaxes.o \
build/2_1/rodread.o \
build/2_1/trees.o \
build/2_1/types.o \
build/2_1/math.o \
build/2_1/magicsys.o \
build/2_1/bitsets.o \
build/2_1/nimsets.o \
build/2_1/passes.o \
build/2_1/treetab.o \
build/2_1/semdata.o \
build/2_1/lookups.o \
build/2_1/importer.o \
build/2_1/rodwrite.o \
build/2_1/semfold.o \
build/2_1/evals.o \
build/2_1/procfind.o \
build/2_1/pragmas.o \
build/4_1/sem.o \
build/2_1/rst.o \
build/2_1/highlite.o \
build/4_1/docgen.o \
build/2_1/ccgutils.o \
build/2_1/cgmeth.o \
build/2_1/cgen.o \
build/2_1/ecmasgen.o \
build/2_1/interact.o \
build/2_1/passaux.o \
build/2_1/depends.o \
build/2_1/transf.o \
build/2_1/main.o \
build/2_1/parseopt.o \
build/2_1/nim__dat.o \
build/2_1/parseutils.o \
build/2_1/strutils.o \
build/4_1/os.o \
build/4_1/nimrod.o"
    $LINKER $LINK_FLAGS -o bin/nimrod  \
build/4_1/system.o \
build/2_1/times.o \
build/3_1/posix.o \
build/2_1/lists.o \
build/2_1/nhashes.o \
build/2_1/nstrtabs.o \
build/4_1/options.o \
build/4_1/msgs.o \
build/2_1/nversion.o \
build/2_1/crc.o \
build/5_1/platform.o \
build/2_1/ropes.o \
build/2_1/idents.o \
build/2_1/ast.o \
build/2_1/astalgo.o \
build/2_1/condsyms.o \
build/2_1/hashes.o \
build/2_1/strtabs.o \
build/2_1/streams.o \
build/3_1/osproc.o \
build/4_1/extccomp.o \
build/2_1/wordrecg.o \
build/4_1/commands.o \
build/2_1/llstream.o \
build/2_1/lexbase.o \
build/2_1/scanner.o \
build/4_1/nimconf.o \
build/2_1/pnimsyn.o \
build/2_1/pbraces.o \
build/2_1/rnimsyn.o \
build/2_1/filters.o \
build/2_1/ptmplsyn.o \
build/4_1/syntaxes.o \
build/2_1/rodread.o \
build/2_1/trees.o \
build/2_1/types.o \
build/2_1/math.o \
build/2_1/magicsys.o \
build/2_1/bitsets.o \
build/2_1/nimsets.o \
build/2_1/passes.o \
build/2_1/treetab.o \
build/2_1/semdata.o \
build/2_1/lookups.o \
build/2_1/importer.o \
build/2_1/rodwrite.o \
build/2_1/semfold.o \
build/2_1/evals.o \
build/2_1/procfind.o \
build/2_1/pragmas.o \
build/4_1/sem.o \
build/2_1/rst.o \
build/2_1/highlite.o \
build/4_1/docgen.o \
build/2_1/ccgutils.o \
build/2_1/cgmeth.o \
build/2_1/cgen.o \
build/2_1/ecmasgen.o \
build/2_1/interact.o \
build/2_1/passaux.o \
build/2_1/depends.o \
build/2_1/transf.o \
build/2_1/main.o \
build/2_1/parseopt.o \
build/2_1/nim__dat.o \
build/2_1/parseutils.o \
build/2_1/strutils.o \
build/4_1/os.o \
build/4_1/nimrod.o || exit 1
    ;;
  amd64)
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/system.c -o build/4_2/system.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/system.c -o build/4_2/system.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/times.c -o build/2_2/times.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/times.c -o build/2_2/times.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_2/posix.c -o build/3_2/posix.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_2/posix.c -o build/3_2/posix.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/lists.c -o build/2_2/lists.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/lists.c -o build/2_2/lists.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nhashes.c -o build/2_2/nhashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nhashes.c -o build/2_2/nhashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nstrtabs.c -o build/2_2/nstrtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nstrtabs.c -o build/2_2/nstrtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/options.c -o build/4_2/options.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/options.c -o build/4_2/options.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/msgs.c -o build/4_2/msgs.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/msgs.c -o build/4_2/msgs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nversion.c -o build/2_2/nversion.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nversion.c -o build/2_2/nversion.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/crc.c -o build/2_2/crc.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/crc.c -o build/2_2/crc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/5_2/platform.c -o build/5_2/platform.o"
    $CC $COMP_FLAGS -Ibuild -c build/5_2/platform.c -o build/5_2/platform.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ropes.c -o build/2_2/ropes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ropes.c -o build/2_2/ropes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/idents.c -o build/2_2/idents.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/idents.c -o build/2_2/idents.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ast.c -o build/2_2/ast.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ast.c -o build/2_2/ast.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/astalgo.c -o build/2_2/astalgo.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/astalgo.c -o build/2_2/astalgo.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/condsyms.c -o build/2_2/condsyms.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/condsyms.c -o build/2_2/condsyms.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/hashes.c -o build/2_2/hashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/hashes.c -o build/2_2/hashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/strtabs.c -o build/2_2/strtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/strtabs.c -o build/2_2/strtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/streams.c -o build/2_2/streams.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/streams.c -o build/2_2/streams.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_2/osproc.c -o build/3_2/osproc.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_2/osproc.c -o build/3_2/osproc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/extccomp.c -o build/4_2/extccomp.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/extccomp.c -o build/4_2/extccomp.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/wordrecg.c -o build/2_2/wordrecg.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/wordrecg.c -o build/2_2/wordrecg.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/commands.c -o build/4_2/commands.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/commands.c -o build/4_2/commands.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/llstream.c -o build/2_2/llstream.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/llstream.c -o build/2_2/llstream.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/lexbase.c -o build/2_2/lexbase.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/lexbase.c -o build/2_2/lexbase.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/scanner.c -o build/2_2/scanner.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/scanner.c -o build/2_2/scanner.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/nimconf.c -o build/4_2/nimconf.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/nimconf.c -o build/4_2/nimconf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/pnimsyn.c -o build/2_2/pnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/pnimsyn.c -o build/2_2/pnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/pbraces.c -o build/2_2/pbraces.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/pbraces.c -o build/2_2/pbraces.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/rnimsyn.c -o build/2_2/rnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/rnimsyn.c -o build/2_2/rnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/filters.c -o build/2_2/filters.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/filters.c -o build/2_2/filters.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ptmplsyn.c -o build/2_2/ptmplsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ptmplsyn.c -o build/2_2/ptmplsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/syntaxes.c -o build/4_2/syntaxes.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/syntaxes.c -o build/4_2/syntaxes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/rodread.c -o build/2_2/rodread.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/rodread.c -o build/2_2/rodread.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/trees.c -o build/2_2/trees.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/trees.c -o build/2_2/trees.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/types.c -o build/2_2/types.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/types.c -o build/2_2/types.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/math.c -o build/2_2/math.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/math.c -o build/2_2/math.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/magicsys.c -o build/2_2/magicsys.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/magicsys.c -o build/2_2/magicsys.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/bitsets.c -o build/2_2/bitsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/bitsets.c -o build/2_2/bitsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nimsets.c -o build/2_2/nimsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nimsets.c -o build/2_2/nimsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/passes.c -o build/2_2/passes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/passes.c -o build/2_2/passes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/treetab.c -o build/2_2/treetab.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/treetab.c -o build/2_2/treetab.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/semdata.c -o build/2_2/semdata.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/semdata.c -o build/2_2/semdata.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/lookups.c -o build/2_2/lookups.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/lookups.c -o build/2_2/lookups.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/importer.c -o build/2_2/importer.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/importer.c -o build/2_2/importer.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/rodwrite.c -o build/2_2/rodwrite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/rodwrite.c -o build/2_2/rodwrite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/semfold.c -o build/2_2/semfold.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/semfold.c -o build/2_2/semfold.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/evals.c -o build/2_2/evals.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/evals.c -o build/2_2/evals.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/procfind.c -o build/2_2/procfind.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/procfind.c -o build/2_2/procfind.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/pragmas.c -o build/2_2/pragmas.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/pragmas.c -o build/2_2/pragmas.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/sem.c -o build/4_2/sem.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/sem.c -o build/4_2/sem.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/rst.c -o build/2_2/rst.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/rst.c -o build/2_2/rst.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/highlite.c -o build/2_2/highlite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/highlite.c -o build/2_2/highlite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/docgen.c -o build/4_2/docgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/docgen.c -o build/4_2/docgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ccgutils.c -o build/2_2/ccgutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ccgutils.c -o build/2_2/ccgutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/cgmeth.c -o build/2_2/cgmeth.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/cgmeth.c -o build/2_2/cgmeth.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/cgen.c -o build/2_2/cgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/cgen.c -o build/2_2/cgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ecmasgen.c -o build/2_2/ecmasgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ecmasgen.c -o build/2_2/ecmasgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/interact.c -o build/2_2/interact.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/interact.c -o build/2_2/interact.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/passaux.c -o build/2_2/passaux.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/passaux.c -o build/2_2/passaux.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/depends.c -o build/2_2/depends.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/depends.c -o build/2_2/depends.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/transf.c -o build/2_2/transf.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/transf.c -o build/2_2/transf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/main.c -o build/2_2/main.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/main.c -o build/2_2/main.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/parseopt.c -o build/2_2/parseopt.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/parseopt.c -o build/2_2/parseopt.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nim__dat.c -o build/2_2/nim__dat.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nim__dat.c -o build/2_2/nim__dat.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/parseutils.c -o build/2_2/parseutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/parseutils.c -o build/2_2/parseutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/strutils.c -o build/2_2/strutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/strutils.c -o build/2_2/strutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/os.c -o build/4_2/os.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/os.c -o build/4_2/os.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/nimrod.c -o build/4_2/nimrod.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/nimrod.c -o build/4_2/nimrod.o || exit 1
    echo "$LINKER $LINK_FLAGS -o bin/nimrod  \
build/4_2/system.o \
build/2_2/times.o \
build/3_2/posix.o \
build/2_2/lists.o \
build/2_2/nhashes.o \
build/2_2/nstrtabs.o \
build/4_2/options.o \
build/4_2/msgs.o \
build/2_2/nversion.o \
build/2_2/crc.o \
build/5_2/platform.o \
build/2_2/ropes.o \
build/2_2/idents.o \
build/2_2/ast.o \
build/2_2/astalgo.o \
build/2_2/condsyms.o \
build/2_2/hashes.o \
build/2_2/strtabs.o \
build/2_2/streams.o \
build/3_2/osproc.o \
build/4_2/extccomp.o \
build/2_2/wordrecg.o \
build/4_2/commands.o \
build/2_2/llstream.o \
build/2_2/lexbase.o \
build/2_2/scanner.o \
build/4_2/nimconf.o \
build/2_2/pnimsyn.o \
build/2_2/pbraces.o \
build/2_2/rnimsyn.o \
build/2_2/filters.o \
build/2_2/ptmplsyn.o \
build/4_2/syntaxes.o \
build/2_2/rodread.o \
build/2_2/trees.o \
build/2_2/types.o \
build/2_2/math.o \
build/2_2/magicsys.o \
build/2_2/bitsets.o \
build/2_2/nimsets.o \
build/2_2/passes.o \
build/2_2/treetab.o \
build/2_2/semdata.o \
build/2_2/lookups.o \
build/2_2/importer.o \
build/2_2/rodwrite.o \
build/2_2/semfold.o \
build/2_2/evals.o \
build/2_2/procfind.o \
build/2_2/pragmas.o \
build/4_2/sem.o \
build/2_2/rst.o \
build/2_2/highlite.o \
build/4_2/docgen.o \
build/2_2/ccgutils.o \
build/2_2/cgmeth.o \
build/2_2/cgen.o \
build/2_2/ecmasgen.o \
build/2_2/interact.o \
build/2_2/passaux.o \
build/2_2/depends.o \
build/2_2/transf.o \
build/2_2/main.o \
build/2_2/parseopt.o \
build/2_2/nim__dat.o \
build/2_2/parseutils.o \
build/2_2/strutils.o \
build/4_2/os.o \
build/4_2/nimrod.o"
    $LINKER $LINK_FLAGS -o bin/nimrod  \
build/4_2/system.o \
build/2_2/times.o \
build/3_2/posix.o \
build/2_2/lists.o \
build/2_2/nhashes.o \
build/2_2/nstrtabs.o \
build/4_2/options.o \
build/4_2/msgs.o \
build/2_2/nversion.o \
build/2_2/crc.o \
build/5_2/platform.o \
build/2_2/ropes.o \
build/2_2/idents.o \
build/2_2/ast.o \
build/2_2/astalgo.o \
build/2_2/condsyms.o \
build/2_2/hashes.o \
build/2_2/strtabs.o \
build/2_2/streams.o \
build/3_2/osproc.o \
build/4_2/extccomp.o \
build/2_2/wordrecg.o \
build/4_2/commands.o \
build/2_2/llstream.o \
build/2_2/lexbase.o \
build/2_2/scanner.o \
build/4_2/nimconf.o \
build/2_2/pnimsyn.o \
build/2_2/pbraces.o \
build/2_2/rnimsyn.o \
build/2_2/filters.o \
build/2_2/ptmplsyn.o \
build/4_2/syntaxes.o \
build/2_2/rodread.o \
build/2_2/trees.o \
build/2_2/types.o \
build/2_2/math.o \
build/2_2/magicsys.o \
build/2_2/bitsets.o \
build/2_2/nimsets.o \
build/2_2/passes.o \
build/2_2/treetab.o \
build/2_2/semdata.o \
build/2_2/lookups.o \
build/2_2/importer.o \
build/2_2/rodwrite.o \
build/2_2/semfold.o \
build/2_2/evals.o \
build/2_2/procfind.o \
build/2_2/pragmas.o \
build/4_2/sem.o \
build/2_2/rst.o \
build/2_2/highlite.o \
build/4_2/docgen.o \
build/2_2/ccgutils.o \
build/2_2/cgmeth.o \
build/2_2/cgen.o \
build/2_2/ecmasgen.o \
build/2_2/interact.o \
build/2_2/passaux.o \
build/2_2/depends.o \
build/2_2/transf.o \
build/2_2/main.o \
build/2_2/parseopt.o \
build/2_2/nim__dat.o \
build/2_2/parseutils.o \
build/2_2/strutils.o \
build/4_2/os.o \
build/4_2/nimrod.o || exit 1
    ;;
  powerpc)
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/system.c -o build/4_1/system.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/system.c -o build/4_1/system.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/times.c -o build/2_1/times.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/times.c -o build/2_1/times.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/posix.c -o build/3_1/posix.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/posix.c -o build/3_1/posix.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lists.c -o build/2_1/lists.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lists.c -o build/2_1/lists.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nhashes.c -o build/2_1/nhashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nhashes.c -o build/2_1/nhashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nstrtabs.c -o build/2_1/nstrtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nstrtabs.c -o build/2_1/nstrtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/options.c -o build/4_3/options.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/options.c -o build/4_3/options.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/msgs.c -o build/4_3/msgs.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/msgs.c -o build/4_3/msgs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nversion.c -o build/2_1/nversion.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nversion.c -o build/2_1/nversion.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/crc.c -o build/2_1/crc.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/crc.c -o build/2_1/crc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/5_3/platform.c -o build/5_3/platform.o"
    $CC $COMP_FLAGS -Ibuild -c build/5_3/platform.c -o build/5_3/platform.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ropes.c -o build/2_1/ropes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ropes.c -o build/2_1/ropes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/idents.c -o build/2_1/idents.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/idents.c -o build/2_1/idents.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/ast.c -o build/2_3/ast.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/ast.c -o build/2_3/ast.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/astalgo.c -o build/2_1/astalgo.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/astalgo.c -o build/2_1/astalgo.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/condsyms.c -o build/2_1/condsyms.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/condsyms.c -o build/2_1/condsyms.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/hashes.c -o build/2_1/hashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/hashes.c -o build/2_1/hashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/strtabs.c -o build/2_1/strtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/strtabs.c -o build/2_1/strtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/streams.c -o build/2_1/streams.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/streams.c -o build/2_1/streams.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/osproc.c -o build/3_1/osproc.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/osproc.c -o build/3_1/osproc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/extccomp.c -o build/4_3/extccomp.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/extccomp.c -o build/4_3/extccomp.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/wordrecg.c -o build/2_1/wordrecg.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/wordrecg.c -o build/2_1/wordrecg.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/commands.c -o build/4_3/commands.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/commands.c -o build/4_3/commands.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/llstream.c -o build/2_1/llstream.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/llstream.c -o build/2_1/llstream.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lexbase.c -o build/2_1/lexbase.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lexbase.c -o build/2_1/lexbase.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/scanner.c -o build/2_1/scanner.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/scanner.c -o build/2_1/scanner.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/nimconf.c -o build/4_1/nimconf.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/nimconf.c -o build/4_1/nimconf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pnimsyn.c -o build/2_1/pnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pnimsyn.c -o build/2_1/pnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pbraces.c -o build/2_1/pbraces.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pbraces.c -o build/2_1/pbraces.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rnimsyn.c -o build/2_1/rnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rnimsyn.c -o build/2_1/rnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/filters.c -o build/2_1/filters.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/filters.c -o build/2_1/filters.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ptmplsyn.c -o build/2_1/ptmplsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ptmplsyn.c -o build/2_1/ptmplsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/syntaxes.c -o build/4_1/syntaxes.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/syntaxes.c -o build/4_1/syntaxes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rodread.c -o build/2_1/rodread.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rodread.c -o build/2_1/rodread.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/trees.c -o build/2_1/trees.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/trees.c -o build/2_1/trees.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/types.c -o build/2_3/types.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/types.c -o build/2_3/types.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/math.c -o build/2_1/math.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/math.c -o build/2_1/math.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/magicsys.c -o build/2_1/magicsys.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/magicsys.c -o build/2_1/magicsys.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/bitsets.c -o build/2_1/bitsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/bitsets.c -o build/2_1/bitsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nimsets.c -o build/2_1/nimsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nimsets.c -o build/2_1/nimsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/passes.c -o build/2_3/passes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/passes.c -o build/2_3/passes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/treetab.c -o build/2_1/treetab.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/treetab.c -o build/2_1/treetab.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/semdata.c -o build/2_1/semdata.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/semdata.c -o build/2_1/semdata.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/lookups.c -o build/2_3/lookups.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/lookups.c -o build/2_3/lookups.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/importer.c -o build/2_3/importer.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/importer.c -o build/2_3/importer.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/rodwrite.c -o build/2_3/rodwrite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/rodwrite.c -o build/2_3/rodwrite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/semfold.c -o build/2_3/semfold.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/semfold.c -o build/2_3/semfold.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/evals.c -o build/2_3/evals.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/evals.c -o build/2_3/evals.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/procfind.c -o build/2_1/procfind.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/procfind.c -o build/2_1/procfind.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/pragmas.c -o build/2_3/pragmas.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/pragmas.c -o build/2_3/pragmas.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/sem.c -o build/4_3/sem.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/sem.c -o build/4_3/sem.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rst.c -o build/2_1/rst.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rst.c -o build/2_1/rst.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/highlite.c -o build/2_1/highlite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/highlite.c -o build/2_1/highlite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/docgen.c -o build/4_1/docgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/docgen.c -o build/4_1/docgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ccgutils.c -o build/2_1/ccgutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ccgutils.c -o build/2_1/ccgutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/cgmeth.c -o build/2_3/cgmeth.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/cgmeth.c -o build/2_3/cgmeth.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/cgen.c -o build/2_3/cgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/cgen.c -o build/2_3/cgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/ecmasgen.c -o build/2_3/ecmasgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/ecmasgen.c -o build/2_3/ecmasgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/interact.c -o build/2_1/interact.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/interact.c -o build/2_1/interact.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/passaux.c -o build/2_1/passaux.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/passaux.c -o build/2_1/passaux.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/depends.c -o build/2_1/depends.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/depends.c -o build/2_1/depends.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/transf.c -o build/2_3/transf.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/transf.c -o build/2_3/transf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/main.c -o build/2_1/main.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/main.c -o build/2_1/main.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/parseopt.c -o build/2_1/parseopt.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/parseopt.c -o build/2_1/parseopt.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nim__dat.c -o build/2_1/nim__dat.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nim__dat.c -o build/2_1/nim__dat.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/parseutils.c -o build/2_1/parseutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/parseutils.c -o build/2_1/parseutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/strutils.c -o build/2_1/strutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/strutils.c -o build/2_1/strutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/os.c -o build/4_1/os.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/os.c -o build/4_1/os.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/nimrod.c -o build/4_3/nimrod.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/nimrod.c -o build/4_3/nimrod.o || exit 1
    echo "$LINKER $LINK_FLAGS -o bin/nimrod  \
build/4_1/system.o \
build/2_1/times.o \
build/3_1/posix.o \
build/2_1/lists.o \
build/2_1/nhashes.o \
build/2_1/nstrtabs.o \
build/4_3/options.o \
build/4_3/msgs.o \
build/2_1/nversion.o \
build/2_1/crc.o \
build/5_3/platform.o \
build/2_1/ropes.o \
build/2_1/idents.o \
build/2_3/ast.o \
build/2_1/astalgo.o \
build/2_1/condsyms.o \
build/2_1/hashes.o \
build/2_1/strtabs.o \
build/2_1/streams.o \
build/3_1/osproc.o \
build/4_3/extccomp.o \
build/2_1/wordrecg.o \
build/4_3/commands.o \
build/2_1/llstream.o \
build/2_1/lexbase.o \
build/2_1/scanner.o \
build/4_1/nimconf.o \
build/2_1/pnimsyn.o \
build/2_1/pbraces.o \
build/2_1/rnimsyn.o \
build/2_1/filters.o \
build/2_1/ptmplsyn.o \
build/4_1/syntaxes.o \
build/2_1/rodread.o \
build/2_1/trees.o \
build/2_3/types.o \
build/2_1/math.o \
build/2_1/magicsys.o \
build/2_1/bitsets.o \
build/2_1/nimsets.o \
build/2_3/passes.o \
build/2_1/treetab.o \
build/2_1/semdata.o \
build/2_3/lookups.o \
build/2_3/importer.o \
build/2_3/rodwrite.o \
build/2_3/semfold.o \
build/2_3/evals.o \
build/2_1/procfind.o \
build/2_3/pragmas.o \
build/4_3/sem.o \
build/2_1/rst.o \
build/2_1/highlite.o \
build/4_1/docgen.o \
build/2_1/ccgutils.o \
build/2_3/cgmeth.o \
build/2_3/cgen.o \
build/2_3/ecmasgen.o \
build/2_1/interact.o \
build/2_1/passaux.o \
build/2_1/depends.o \
build/2_3/transf.o \
build/2_1/main.o \
build/2_1/parseopt.o \
build/2_1/nim__dat.o \
build/2_1/parseutils.o \
build/2_1/strutils.o \
build/4_1/os.o \
build/4_3/nimrod.o"
    $LINKER $LINK_FLAGS -o bin/nimrod  \
build/4_1/system.o \
build/2_1/times.o \
build/3_1/posix.o \
build/2_1/lists.o \
build/2_1/nhashes.o \
build/2_1/nstrtabs.o \
build/4_3/options.o \
build/4_3/msgs.o \
build/2_1/nversion.o \
build/2_1/crc.o \
build/5_3/platform.o \
build/2_1/ropes.o \
build/2_1/idents.o \
build/2_3/ast.o \
build/2_1/astalgo.o \
build/2_1/condsyms.o \
build/2_1/hashes.o \
build/2_1/strtabs.o \
build/2_1/streams.o \
build/3_1/osproc.o \
build/4_3/extccomp.o \
build/2_1/wordrecg.o \
build/4_3/commands.o \
build/2_1/llstream.o \
build/2_1/lexbase.o \
build/2_1/scanner.o \
build/4_1/nimconf.o \
build/2_1/pnimsyn.o \
build/2_1/pbraces.o \
build/2_1/rnimsyn.o \
build/2_1/filters.o \
build/2_1/ptmplsyn.o \
build/4_1/syntaxes.o \
build/2_1/rodread.o \
build/2_1/trees.o \
build/2_3/types.o \
build/2_1/math.o \
build/2_1/magicsys.o \
build/2_1/bitsets.o \
build/2_1/nimsets.o \
build/2_3/passes.o \
build/2_1/treetab.o \
build/2_1/semdata.o \
build/2_3/lookups.o \
build/2_3/importer.o \
build/2_3/rodwrite.o \
build/2_3/semfold.o \
build/2_3/evals.o \
build/2_1/procfind.o \
build/2_3/pragmas.o \
build/4_3/sem.o \
build/2_1/rst.o \
build/2_1/highlite.o \
build/4_1/docgen.o \
build/2_1/ccgutils.o \
build/2_3/cgmeth.o \
build/2_3/cgen.o \
build/2_3/ecmasgen.o \
build/2_1/interact.o \
build/2_1/passaux.o \
build/2_1/depends.o \
build/2_3/transf.o \
build/2_1/main.o \
build/2_1/parseopt.o \
build/2_1/nim__dat.o \
build/2_1/parseutils.o \
build/2_1/strutils.o \
build/4_1/os.o \
build/4_3/nimrod.o || exit 1
    ;;
  *)
    echo "Error: no C code generated for: [$myos: $mycpu]"
    exit 1
    ;;
  esac
  ;;
openbsd) 
  case $mycpu in
  i386)
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/system.c -o build/4_1/system.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/system.c -o build/4_1/system.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/times.c -o build/2_1/times.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/times.c -o build/2_1/times.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/posix.c -o build/3_1/posix.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/posix.c -o build/3_1/posix.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lists.c -o build/2_1/lists.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lists.c -o build/2_1/lists.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nhashes.c -o build/2_1/nhashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nhashes.c -o build/2_1/nhashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nstrtabs.c -o build/2_1/nstrtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nstrtabs.c -o build/2_1/nstrtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/options.c -o build/4_1/options.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/options.c -o build/4_1/options.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/msgs.c -o build/4_1/msgs.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/msgs.c -o build/4_1/msgs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nversion.c -o build/2_1/nversion.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nversion.c -o build/2_1/nversion.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/crc.c -o build/2_1/crc.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/crc.c -o build/2_1/crc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/6_1/platform.c -o build/6_1/platform.o"
    $CC $COMP_FLAGS -Ibuild -c build/6_1/platform.c -o build/6_1/platform.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ropes.c -o build/2_1/ropes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ropes.c -o build/2_1/ropes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/idents.c -o build/2_1/idents.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/idents.c -o build/2_1/idents.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ast.c -o build/2_1/ast.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ast.c -o build/2_1/ast.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/astalgo.c -o build/2_1/astalgo.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/astalgo.c -o build/2_1/astalgo.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/condsyms.c -o build/2_1/condsyms.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/condsyms.c -o build/2_1/condsyms.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/hashes.c -o build/2_1/hashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/hashes.c -o build/2_1/hashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/strtabs.c -o build/2_1/strtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/strtabs.c -o build/2_1/strtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/streams.c -o build/2_1/streams.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/streams.c -o build/2_1/streams.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/osproc.c -o build/3_1/osproc.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/osproc.c -o build/3_1/osproc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/extccomp.c -o build/4_1/extccomp.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/extccomp.c -o build/4_1/extccomp.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/wordrecg.c -o build/2_1/wordrecg.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/wordrecg.c -o build/2_1/wordrecg.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/commands.c -o build/4_1/commands.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/commands.c -o build/4_1/commands.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/llstream.c -o build/2_1/llstream.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/llstream.c -o build/2_1/llstream.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lexbase.c -o build/2_1/lexbase.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lexbase.c -o build/2_1/lexbase.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/scanner.c -o build/2_1/scanner.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/scanner.c -o build/2_1/scanner.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/nimconf.c -o build/4_1/nimconf.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/nimconf.c -o build/4_1/nimconf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pnimsyn.c -o build/2_1/pnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pnimsyn.c -o build/2_1/pnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pbraces.c -o build/2_1/pbraces.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pbraces.c -o build/2_1/pbraces.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rnimsyn.c -o build/2_1/rnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rnimsyn.c -o build/2_1/rnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/filters.c -o build/2_1/filters.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/filters.c -o build/2_1/filters.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ptmplsyn.c -o build/2_1/ptmplsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ptmplsyn.c -o build/2_1/ptmplsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/syntaxes.c -o build/4_1/syntaxes.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/syntaxes.c -o build/4_1/syntaxes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rodread.c -o build/2_1/rodread.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rodread.c -o build/2_1/rodread.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/trees.c -o build/2_1/trees.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/trees.c -o build/2_1/trees.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/types.c -o build/2_1/types.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/types.c -o build/2_1/types.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/math.c -o build/2_1/math.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/math.c -o build/2_1/math.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/magicsys.c -o build/2_1/magicsys.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/magicsys.c -o build/2_1/magicsys.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/bitsets.c -o build/2_1/bitsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/bitsets.c -o build/2_1/bitsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nimsets.c -o build/2_1/nimsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nimsets.c -o build/2_1/nimsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/passes.c -o build/2_1/passes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/passes.c -o build/2_1/passes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/treetab.c -o build/2_1/treetab.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/treetab.c -o build/2_1/treetab.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/semdata.c -o build/2_1/semdata.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/semdata.c -o build/2_1/semdata.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lookups.c -o build/2_1/lookups.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lookups.c -o build/2_1/lookups.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/importer.c -o build/2_1/importer.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/importer.c -o build/2_1/importer.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rodwrite.c -o build/2_1/rodwrite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rodwrite.c -o build/2_1/rodwrite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/semfold.c -o build/2_1/semfold.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/semfold.c -o build/2_1/semfold.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/evals.c -o build/2_1/evals.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/evals.c -o build/2_1/evals.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/procfind.c -o build/2_1/procfind.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/procfind.c -o build/2_1/procfind.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pragmas.c -o build/2_1/pragmas.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pragmas.c -o build/2_1/pragmas.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/sem.c -o build/4_1/sem.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/sem.c -o build/4_1/sem.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rst.c -o build/2_1/rst.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rst.c -o build/2_1/rst.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/highlite.c -o build/2_1/highlite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/highlite.c -o build/2_1/highlite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/docgen.c -o build/4_1/docgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/docgen.c -o build/4_1/docgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ccgutils.c -o build/2_1/ccgutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ccgutils.c -o build/2_1/ccgutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/cgmeth.c -o build/2_1/cgmeth.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/cgmeth.c -o build/2_1/cgmeth.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/cgen.c -o build/2_1/cgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/cgen.c -o build/2_1/cgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ecmasgen.c -o build/2_1/ecmasgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ecmasgen.c -o build/2_1/ecmasgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/interact.c -o build/2_1/interact.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/interact.c -o build/2_1/interact.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/passaux.c -o build/2_1/passaux.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/passaux.c -o build/2_1/passaux.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/depends.c -o build/2_1/depends.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/depends.c -o build/2_1/depends.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/transf.c -o build/2_1/transf.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/transf.c -o build/2_1/transf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/main.c -o build/2_1/main.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/main.c -o build/2_1/main.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/parseopt.c -o build/2_1/parseopt.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/parseopt.c -o build/2_1/parseopt.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nim__dat.c -o build/2_1/nim__dat.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nim__dat.c -o build/2_1/nim__dat.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/parseutils.c -o build/2_1/parseutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/parseutils.c -o build/2_1/parseutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/strutils.c -o build/2_1/strutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/strutils.c -o build/2_1/strutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/os.c -o build/4_1/os.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/os.c -o build/4_1/os.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/nimrod.c -o build/4_1/nimrod.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/nimrod.c -o build/4_1/nimrod.o || exit 1
    echo "$LINKER $LINK_FLAGS -o bin/nimrod  \
build/4_1/system.o \
build/2_1/times.o \
build/3_1/posix.o \
build/2_1/lists.o \
build/2_1/nhashes.o \
build/2_1/nstrtabs.o \
build/4_1/options.o \
build/4_1/msgs.o \
build/2_1/nversion.o \
build/2_1/crc.o \
build/6_1/platform.o \
build/2_1/ropes.o \
build/2_1/idents.o \
build/2_1/ast.o \
build/2_1/astalgo.o \
build/2_1/condsyms.o \
build/2_1/hashes.o \
build/2_1/strtabs.o \
build/2_1/streams.o \
build/3_1/osproc.o \
build/4_1/extccomp.o \
build/2_1/wordrecg.o \
build/4_1/commands.o \
build/2_1/llstream.o \
build/2_1/lexbase.o \
build/2_1/scanner.o \
build/4_1/nimconf.o \
build/2_1/pnimsyn.o \
build/2_1/pbraces.o \
build/2_1/rnimsyn.o \
build/2_1/filters.o \
build/2_1/ptmplsyn.o \
build/4_1/syntaxes.o \
build/2_1/rodread.o \
build/2_1/trees.o \
build/2_1/types.o \
build/2_1/math.o \
build/2_1/magicsys.o \
build/2_1/bitsets.o \
build/2_1/nimsets.o \
build/2_1/passes.o \
build/2_1/treetab.o \
build/2_1/semdata.o \
build/2_1/lookups.o \
build/2_1/importer.o \
build/2_1/rodwrite.o \
build/2_1/semfold.o \
build/2_1/evals.o \
build/2_1/procfind.o \
build/2_1/pragmas.o \
build/4_1/sem.o \
build/2_1/rst.o \
build/2_1/highlite.o \
build/4_1/docgen.o \
build/2_1/ccgutils.o \
build/2_1/cgmeth.o \
build/2_1/cgen.o \
build/2_1/ecmasgen.o \
build/2_1/interact.o \
build/2_1/passaux.o \
build/2_1/depends.o \
build/2_1/transf.o \
build/2_1/main.o \
build/2_1/parseopt.o \
build/2_1/nim__dat.o \
build/2_1/parseutils.o \
build/2_1/strutils.o \
build/4_1/os.o \
build/4_1/nimrod.o"
    $LINKER $LINK_FLAGS -o bin/nimrod  \
build/4_1/system.o \
build/2_1/times.o \
build/3_1/posix.o \
build/2_1/lists.o \
build/2_1/nhashes.o \
build/2_1/nstrtabs.o \
build/4_1/options.o \
build/4_1/msgs.o \
build/2_1/nversion.o \
build/2_1/crc.o \
build/6_1/platform.o \
build/2_1/ropes.o \
build/2_1/idents.o \
build/2_1/ast.o \
build/2_1/astalgo.o \
build/2_1/condsyms.o \
build/2_1/hashes.o \
build/2_1/strtabs.o \
build/2_1/streams.o \
build/3_1/osproc.o \
build/4_1/extccomp.o \
build/2_1/wordrecg.o \
build/4_1/commands.o \
build/2_1/llstream.o \
build/2_1/lexbase.o \
build/2_1/scanner.o \
build/4_1/nimconf.o \
build/2_1/pnimsyn.o \
build/2_1/pbraces.o \
build/2_1/rnimsyn.o \
build/2_1/filters.o \
build/2_1/ptmplsyn.o \
build/4_1/syntaxes.o \
build/2_1/rodread.o \
build/2_1/trees.o \
build/2_1/types.o \
build/2_1/math.o \
build/2_1/magicsys.o \
build/2_1/bitsets.o \
build/2_1/nimsets.o \
build/2_1/passes.o \
build/2_1/treetab.o \
build/2_1/semdata.o \
build/2_1/lookups.o \
build/2_1/importer.o \
build/2_1/rodwrite.o \
build/2_1/semfold.o \
build/2_1/evals.o \
build/2_1/procfind.o \
build/2_1/pragmas.o \
build/4_1/sem.o \
build/2_1/rst.o \
build/2_1/highlite.o \
build/4_1/docgen.o \
build/2_1/ccgutils.o \
build/2_1/cgmeth.o \
build/2_1/cgen.o \
build/2_1/ecmasgen.o \
build/2_1/interact.o \
build/2_1/passaux.o \
build/2_1/depends.o \
build/2_1/transf.o \
build/2_1/main.o \
build/2_1/parseopt.o \
build/2_1/nim__dat.o \
build/2_1/parseutils.o \
build/2_1/strutils.o \
build/4_1/os.o \
build/4_1/nimrod.o || exit 1
    ;;
  amd64)
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/system.c -o build/4_2/system.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/system.c -o build/4_2/system.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/times.c -o build/2_2/times.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/times.c -o build/2_2/times.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_2/posix.c -o build/3_2/posix.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_2/posix.c -o build/3_2/posix.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/lists.c -o build/2_2/lists.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/lists.c -o build/2_2/lists.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nhashes.c -o build/2_2/nhashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nhashes.c -o build/2_2/nhashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nstrtabs.c -o build/2_2/nstrtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nstrtabs.c -o build/2_2/nstrtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/options.c -o build/4_2/options.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/options.c -o build/4_2/options.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/msgs.c -o build/4_2/msgs.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/msgs.c -o build/4_2/msgs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nversion.c -o build/2_2/nversion.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nversion.c -o build/2_2/nversion.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/crc.c -o build/2_2/crc.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/crc.c -o build/2_2/crc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/6_2/platform.c -o build/6_2/platform.o"
    $CC $COMP_FLAGS -Ibuild -c build/6_2/platform.c -o build/6_2/platform.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ropes.c -o build/2_2/ropes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ropes.c -o build/2_2/ropes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/idents.c -o build/2_2/idents.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/idents.c -o build/2_2/idents.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ast.c -o build/2_2/ast.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ast.c -o build/2_2/ast.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/astalgo.c -o build/2_2/astalgo.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/astalgo.c -o build/2_2/astalgo.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/condsyms.c -o build/2_2/condsyms.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/condsyms.c -o build/2_2/condsyms.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/hashes.c -o build/2_2/hashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/hashes.c -o build/2_2/hashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/strtabs.c -o build/2_2/strtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/strtabs.c -o build/2_2/strtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/streams.c -o build/2_2/streams.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/streams.c -o build/2_2/streams.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_2/osproc.c -o build/3_2/osproc.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_2/osproc.c -o build/3_2/osproc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/extccomp.c -o build/4_2/extccomp.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/extccomp.c -o build/4_2/extccomp.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/wordrecg.c -o build/2_2/wordrecg.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/wordrecg.c -o build/2_2/wordrecg.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/commands.c -o build/4_2/commands.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/commands.c -o build/4_2/commands.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/llstream.c -o build/2_2/llstream.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/llstream.c -o build/2_2/llstream.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/lexbase.c -o build/2_2/lexbase.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/lexbase.c -o build/2_2/lexbase.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/scanner.c -o build/2_2/scanner.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/scanner.c -o build/2_2/scanner.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/nimconf.c -o build/4_2/nimconf.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/nimconf.c -o build/4_2/nimconf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/pnimsyn.c -o build/2_2/pnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/pnimsyn.c -o build/2_2/pnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/pbraces.c -o build/2_2/pbraces.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/pbraces.c -o build/2_2/pbraces.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/rnimsyn.c -o build/2_2/rnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/rnimsyn.c -o build/2_2/rnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/filters.c -o build/2_2/filters.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/filters.c -o build/2_2/filters.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ptmplsyn.c -o build/2_2/ptmplsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ptmplsyn.c -o build/2_2/ptmplsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/syntaxes.c -o build/4_2/syntaxes.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/syntaxes.c -o build/4_2/syntaxes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/rodread.c -o build/2_2/rodread.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/rodread.c -o build/2_2/rodread.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/trees.c -o build/2_2/trees.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/trees.c -o build/2_2/trees.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/types.c -o build/2_2/types.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/types.c -o build/2_2/types.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/math.c -o build/2_2/math.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/math.c -o build/2_2/math.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/magicsys.c -o build/2_2/magicsys.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/magicsys.c -o build/2_2/magicsys.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/bitsets.c -o build/2_2/bitsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/bitsets.c -o build/2_2/bitsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nimsets.c -o build/2_2/nimsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nimsets.c -o build/2_2/nimsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/passes.c -o build/2_2/passes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/passes.c -o build/2_2/passes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/treetab.c -o build/2_2/treetab.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/treetab.c -o build/2_2/treetab.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/semdata.c -o build/2_2/semdata.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/semdata.c -o build/2_2/semdata.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/lookups.c -o build/2_2/lookups.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/lookups.c -o build/2_2/lookups.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/importer.c -o build/2_2/importer.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/importer.c -o build/2_2/importer.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/rodwrite.c -o build/2_2/rodwrite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/rodwrite.c -o build/2_2/rodwrite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/semfold.c -o build/2_2/semfold.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/semfold.c -o build/2_2/semfold.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/evals.c -o build/2_2/evals.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/evals.c -o build/2_2/evals.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/procfind.c -o build/2_2/procfind.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/procfind.c -o build/2_2/procfind.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/pragmas.c -o build/2_2/pragmas.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/pragmas.c -o build/2_2/pragmas.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/sem.c -o build/4_2/sem.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/sem.c -o build/4_2/sem.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/rst.c -o build/2_2/rst.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/rst.c -o build/2_2/rst.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/highlite.c -o build/2_2/highlite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/highlite.c -o build/2_2/highlite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/docgen.c -o build/4_2/docgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/docgen.c -o build/4_2/docgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ccgutils.c -o build/2_2/ccgutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ccgutils.c -o build/2_2/ccgutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/cgmeth.c -o build/2_2/cgmeth.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/cgmeth.c -o build/2_2/cgmeth.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/cgen.c -o build/2_2/cgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/cgen.c -o build/2_2/cgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ecmasgen.c -o build/2_2/ecmasgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ecmasgen.c -o build/2_2/ecmasgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/interact.c -o build/2_2/interact.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/interact.c -o build/2_2/interact.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/passaux.c -o build/2_2/passaux.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/passaux.c -o build/2_2/passaux.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/depends.c -o build/2_2/depends.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/depends.c -o build/2_2/depends.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/transf.c -o build/2_2/transf.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/transf.c -o build/2_2/transf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/main.c -o build/2_2/main.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/main.c -o build/2_2/main.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/parseopt.c -o build/2_2/parseopt.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/parseopt.c -o build/2_2/parseopt.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nim__dat.c -o build/2_2/nim__dat.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nim__dat.c -o build/2_2/nim__dat.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/parseutils.c -o build/2_2/parseutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/parseutils.c -o build/2_2/parseutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/strutils.c -o build/2_2/strutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/strutils.c -o build/2_2/strutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/os.c -o build/4_2/os.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/os.c -o build/4_2/os.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/nimrod.c -o build/4_2/nimrod.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/nimrod.c -o build/4_2/nimrod.o || exit 1
    echo "$LINKER $LINK_FLAGS -o bin/nimrod  \
build/4_2/system.o \
build/2_2/times.o \
build/3_2/posix.o \
build/2_2/lists.o \
build/2_2/nhashes.o \
build/2_2/nstrtabs.o \
build/4_2/options.o \
build/4_2/msgs.o \
build/2_2/nversion.o \
build/2_2/crc.o \
build/6_2/platform.o \
build/2_2/ropes.o \
build/2_2/idents.o \
build/2_2/ast.o \
build/2_2/astalgo.o \
build/2_2/condsyms.o \
build/2_2/hashes.o \
build/2_2/strtabs.o \
build/2_2/streams.o \
build/3_2/osproc.o \
build/4_2/extccomp.o \
build/2_2/wordrecg.o \
build/4_2/commands.o \
build/2_2/llstream.o \
build/2_2/lexbase.o \
build/2_2/scanner.o \
build/4_2/nimconf.o \
build/2_2/pnimsyn.o \
build/2_2/pbraces.o \
build/2_2/rnimsyn.o \
build/2_2/filters.o \
build/2_2/ptmplsyn.o \
build/4_2/syntaxes.o \
build/2_2/rodread.o \
build/2_2/trees.o \
build/2_2/types.o \
build/2_2/math.o \
build/2_2/magicsys.o \
build/2_2/bitsets.o \
build/2_2/nimsets.o \
build/2_2/passes.o \
build/2_2/treetab.o \
build/2_2/semdata.o \
build/2_2/lookups.o \
build/2_2/importer.o \
build/2_2/rodwrite.o \
build/2_2/semfold.o \
build/2_2/evals.o \
build/2_2/procfind.o \
build/2_2/pragmas.o \
build/4_2/sem.o \
build/2_2/rst.o \
build/2_2/highlite.o \
build/4_2/docgen.o \
build/2_2/ccgutils.o \
build/2_2/cgmeth.o \
build/2_2/cgen.o \
build/2_2/ecmasgen.o \
build/2_2/interact.o \
build/2_2/passaux.o \
build/2_2/depends.o \
build/2_2/transf.o \
build/2_2/main.o \
build/2_2/parseopt.o \
build/2_2/nim__dat.o \
build/2_2/parseutils.o \
build/2_2/strutils.o \
build/4_2/os.o \
build/4_2/nimrod.o"
    $LINKER $LINK_FLAGS -o bin/nimrod  \
build/4_2/system.o \
build/2_2/times.o \
build/3_2/posix.o \
build/2_2/lists.o \
build/2_2/nhashes.o \
build/2_2/nstrtabs.o \
build/4_2/options.o \
build/4_2/msgs.o \
build/2_2/nversion.o \
build/2_2/crc.o \
build/6_2/platform.o \
build/2_2/ropes.o \
build/2_2/idents.o \
build/2_2/ast.o \
build/2_2/astalgo.o \
build/2_2/condsyms.o \
build/2_2/hashes.o \
build/2_2/strtabs.o \
build/2_2/streams.o \
build/3_2/osproc.o \
build/4_2/extccomp.o \
build/2_2/wordrecg.o \
build/4_2/commands.o \
build/2_2/llstream.o \
build/2_2/lexbase.o \
build/2_2/scanner.o \
build/4_2/nimconf.o \
build/2_2/pnimsyn.o \
build/2_2/pbraces.o \
build/2_2/rnimsyn.o \
build/2_2/filters.o \
build/2_2/ptmplsyn.o \
build/4_2/syntaxes.o \
build/2_2/rodread.o \
build/2_2/trees.o \
build/2_2/types.o \
build/2_2/math.o \
build/2_2/magicsys.o \
build/2_2/bitsets.o \
build/2_2/nimsets.o \
build/2_2/passes.o \
build/2_2/treetab.o \
build/2_2/semdata.o \
build/2_2/lookups.o \
build/2_2/importer.o \
build/2_2/rodwrite.o \
build/2_2/semfold.o \
build/2_2/evals.o \
build/2_2/procfind.o \
build/2_2/pragmas.o \
build/4_2/sem.o \
build/2_2/rst.o \
build/2_2/highlite.o \
build/4_2/docgen.o \
build/2_2/ccgutils.o \
build/2_2/cgmeth.o \
build/2_2/cgen.o \
build/2_2/ecmasgen.o \
build/2_2/interact.o \
build/2_2/passaux.o \
build/2_2/depends.o \
build/2_2/transf.o \
build/2_2/main.o \
build/2_2/parseopt.o \
build/2_2/nim__dat.o \
build/2_2/parseutils.o \
build/2_2/strutils.o \
build/4_2/os.o \
build/4_2/nimrod.o || exit 1
    ;;
  powerpc)
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/system.c -o build/4_1/system.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/system.c -o build/4_1/system.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/times.c -o build/2_1/times.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/times.c -o build/2_1/times.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/posix.c -o build/3_1/posix.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/posix.c -o build/3_1/posix.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lists.c -o build/2_1/lists.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lists.c -o build/2_1/lists.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nhashes.c -o build/2_1/nhashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nhashes.c -o build/2_1/nhashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nstrtabs.c -o build/2_1/nstrtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nstrtabs.c -o build/2_1/nstrtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/options.c -o build/4_3/options.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/options.c -o build/4_3/options.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/msgs.c -o build/4_3/msgs.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/msgs.c -o build/4_3/msgs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nversion.c -o build/2_1/nversion.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nversion.c -o build/2_1/nversion.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/crc.c -o build/2_1/crc.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/crc.c -o build/2_1/crc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/6_3/platform.c -o build/6_3/platform.o"
    $CC $COMP_FLAGS -Ibuild -c build/6_3/platform.c -o build/6_3/platform.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ropes.c -o build/2_1/ropes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ropes.c -o build/2_1/ropes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/idents.c -o build/2_1/idents.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/idents.c -o build/2_1/idents.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/ast.c -o build/2_3/ast.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/ast.c -o build/2_3/ast.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/astalgo.c -o build/2_1/astalgo.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/astalgo.c -o build/2_1/astalgo.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/condsyms.c -o build/2_1/condsyms.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/condsyms.c -o build/2_1/condsyms.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/hashes.c -o build/2_1/hashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/hashes.c -o build/2_1/hashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/strtabs.c -o build/2_1/strtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/strtabs.c -o build/2_1/strtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/streams.c -o build/2_1/streams.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/streams.c -o build/2_1/streams.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/osproc.c -o build/3_1/osproc.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/osproc.c -o build/3_1/osproc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/extccomp.c -o build/4_3/extccomp.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/extccomp.c -o build/4_3/extccomp.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/wordrecg.c -o build/2_1/wordrecg.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/wordrecg.c -o build/2_1/wordrecg.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/commands.c -o build/4_3/commands.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/commands.c -o build/4_3/commands.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/llstream.c -o build/2_1/llstream.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/llstream.c -o build/2_1/llstream.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lexbase.c -o build/2_1/lexbase.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lexbase.c -o build/2_1/lexbase.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/scanner.c -o build/2_1/scanner.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/scanner.c -o build/2_1/scanner.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/nimconf.c -o build/4_1/nimconf.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/nimconf.c -o build/4_1/nimconf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pnimsyn.c -o build/2_1/pnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pnimsyn.c -o build/2_1/pnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pbraces.c -o build/2_1/pbraces.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pbraces.c -o build/2_1/pbraces.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rnimsyn.c -o build/2_1/rnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rnimsyn.c -o build/2_1/rnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/filters.c -o build/2_1/filters.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/filters.c -o build/2_1/filters.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ptmplsyn.c -o build/2_1/ptmplsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ptmplsyn.c -o build/2_1/ptmplsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/syntaxes.c -o build/4_1/syntaxes.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/syntaxes.c -o build/4_1/syntaxes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rodread.c -o build/2_1/rodread.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rodread.c -o build/2_1/rodread.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/trees.c -o build/2_1/trees.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/trees.c -o build/2_1/trees.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/types.c -o build/2_3/types.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/types.c -o build/2_3/types.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/math.c -o build/2_1/math.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/math.c -o build/2_1/math.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/magicsys.c -o build/2_1/magicsys.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/magicsys.c -o build/2_1/magicsys.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/bitsets.c -o build/2_1/bitsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/bitsets.c -o build/2_1/bitsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nimsets.c -o build/2_1/nimsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nimsets.c -o build/2_1/nimsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/passes.c -o build/2_3/passes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/passes.c -o build/2_3/passes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/treetab.c -o build/2_1/treetab.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/treetab.c -o build/2_1/treetab.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/semdata.c -o build/2_1/semdata.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/semdata.c -o build/2_1/semdata.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/lookups.c -o build/2_3/lookups.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/lookups.c -o build/2_3/lookups.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/importer.c -o build/2_3/importer.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/importer.c -o build/2_3/importer.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/rodwrite.c -o build/2_3/rodwrite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/rodwrite.c -o build/2_3/rodwrite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/semfold.c -o build/2_3/semfold.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/semfold.c -o build/2_3/semfold.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/evals.c -o build/2_3/evals.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/evals.c -o build/2_3/evals.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/procfind.c -o build/2_1/procfind.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/procfind.c -o build/2_1/procfind.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/pragmas.c -o build/2_3/pragmas.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/pragmas.c -o build/2_3/pragmas.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/sem.c -o build/4_3/sem.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/sem.c -o build/4_3/sem.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rst.c -o build/2_1/rst.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rst.c -o build/2_1/rst.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/highlite.c -o build/2_1/highlite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/highlite.c -o build/2_1/highlite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/docgen.c -o build/4_1/docgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/docgen.c -o build/4_1/docgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ccgutils.c -o build/2_1/ccgutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ccgutils.c -o build/2_1/ccgutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/cgmeth.c -o build/2_3/cgmeth.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/cgmeth.c -o build/2_3/cgmeth.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/cgen.c -o build/2_3/cgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/cgen.c -o build/2_3/cgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/ecmasgen.c -o build/2_3/ecmasgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/ecmasgen.c -o build/2_3/ecmasgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/interact.c -o build/2_1/interact.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/interact.c -o build/2_1/interact.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/passaux.c -o build/2_1/passaux.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/passaux.c -o build/2_1/passaux.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/depends.c -o build/2_1/depends.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/depends.c -o build/2_1/depends.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/transf.c -o build/2_3/transf.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/transf.c -o build/2_3/transf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/main.c -o build/2_1/main.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/main.c -o build/2_1/main.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/parseopt.c -o build/2_1/parseopt.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/parseopt.c -o build/2_1/parseopt.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nim__dat.c -o build/2_1/nim__dat.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nim__dat.c -o build/2_1/nim__dat.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/parseutils.c -o build/2_1/parseutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/parseutils.c -o build/2_1/parseutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/strutils.c -o build/2_1/strutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/strutils.c -o build/2_1/strutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/os.c -o build/4_1/os.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/os.c -o build/4_1/os.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/nimrod.c -o build/4_3/nimrod.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/nimrod.c -o build/4_3/nimrod.o || exit 1
    echo "$LINKER $LINK_FLAGS -o bin/nimrod  \
build/4_1/system.o \
build/2_1/times.o \
build/3_1/posix.o \
build/2_1/lists.o \
build/2_1/nhashes.o \
build/2_1/nstrtabs.o \
build/4_3/options.o \
build/4_3/msgs.o \
build/2_1/nversion.o \
build/2_1/crc.o \
build/6_3/platform.o \
build/2_1/ropes.o \
build/2_1/idents.o \
build/2_3/ast.o \
build/2_1/astalgo.o \
build/2_1/condsyms.o \
build/2_1/hashes.o \
build/2_1/strtabs.o \
build/2_1/streams.o \
build/3_1/osproc.o \
build/4_3/extccomp.o \
build/2_1/wordrecg.o \
build/4_3/commands.o \
build/2_1/llstream.o \
build/2_1/lexbase.o \
build/2_1/scanner.o \
build/4_1/nimconf.o \
build/2_1/pnimsyn.o \
build/2_1/pbraces.o \
build/2_1/rnimsyn.o \
build/2_1/filters.o \
build/2_1/ptmplsyn.o \
build/4_1/syntaxes.o \
build/2_1/rodread.o \
build/2_1/trees.o \
build/2_3/types.o \
build/2_1/math.o \
build/2_1/magicsys.o \
build/2_1/bitsets.o \
build/2_1/nimsets.o \
build/2_3/passes.o \
build/2_1/treetab.o \
build/2_1/semdata.o \
build/2_3/lookups.o \
build/2_3/importer.o \
build/2_3/rodwrite.o \
build/2_3/semfold.o \
build/2_3/evals.o \
build/2_1/procfind.o \
build/2_3/pragmas.o \
build/4_3/sem.o \
build/2_1/rst.o \
build/2_1/highlite.o \
build/4_1/docgen.o \
build/2_1/ccgutils.o \
build/2_3/cgmeth.o \
build/2_3/cgen.o \
build/2_3/ecmasgen.o \
build/2_1/interact.o \
build/2_1/passaux.o \
build/2_1/depends.o \
build/2_3/transf.o \
build/2_1/main.o \
build/2_1/parseopt.o \
build/2_1/nim__dat.o \
build/2_1/parseutils.o \
build/2_1/strutils.o \
build/4_1/os.o \
build/4_3/nimrod.o"
    $LINKER $LINK_FLAGS -o bin/nimrod  \
build/4_1/system.o \
build/2_1/times.o \
build/3_1/posix.o \
build/2_1/lists.o \
build/2_1/nhashes.o \
build/2_1/nstrtabs.o \
build/4_3/options.o \
build/4_3/msgs.o \
build/2_1/nversion.o \
build/2_1/crc.o \
build/6_3/platform.o \
build/2_1/ropes.o \
build/2_1/idents.o \
build/2_3/ast.o \
build/2_1/astalgo.o \
build/2_1/condsyms.o \
build/2_1/hashes.o \
build/2_1/strtabs.o \
build/2_1/streams.o \
build/3_1/osproc.o \
build/4_3/extccomp.o \
build/2_1/wordrecg.o \
build/4_3/commands.o \
build/2_1/llstream.o \
build/2_1/lexbase.o \
build/2_1/scanner.o \
build/4_1/nimconf.o \
build/2_1/pnimsyn.o \
build/2_1/pbraces.o \
build/2_1/rnimsyn.o \
build/2_1/filters.o \
build/2_1/ptmplsyn.o \
build/4_1/syntaxes.o \
build/2_1/rodread.o \
build/2_1/trees.o \
build/2_3/types.o \
build/2_1/math.o \
build/2_1/magicsys.o \
build/2_1/bitsets.o \
build/2_1/nimsets.o \
build/2_3/passes.o \
build/2_1/treetab.o \
build/2_1/semdata.o \
build/2_3/lookups.o \
build/2_3/importer.o \
build/2_3/rodwrite.o \
build/2_3/semfold.o \
build/2_3/evals.o \
build/2_1/procfind.o \
build/2_3/pragmas.o \
build/4_3/sem.o \
build/2_1/rst.o \
build/2_1/highlite.o \
build/4_1/docgen.o \
build/2_1/ccgutils.o \
build/2_3/cgmeth.o \
build/2_3/cgen.o \
build/2_3/ecmasgen.o \
build/2_1/interact.o \
build/2_1/passaux.o \
build/2_1/depends.o \
build/2_3/transf.o \
build/2_1/main.o \
build/2_1/parseopt.o \
build/2_1/nim__dat.o \
build/2_1/parseutils.o \
build/2_1/strutils.o \
build/4_1/os.o \
build/4_3/nimrod.o || exit 1
    ;;
  *)
    echo "Error: no C code generated for: [$myos: $mycpu]"
    exit 1
    ;;
  esac
  ;;
solaris) 
  case $mycpu in
  i386)
    echo "$CC $COMP_FLAGS -Ibuild -c build/7_1/system.c -o build/7_1/system.o"
    $CC $COMP_FLAGS -Ibuild -c build/7_1/system.c -o build/7_1/system.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/times.c -o build/2_1/times.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/times.c -o build/2_1/times.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/posix.c -o build/3_1/posix.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/posix.c -o build/3_1/posix.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lists.c -o build/2_1/lists.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lists.c -o build/2_1/lists.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nhashes.c -o build/2_1/nhashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nhashes.c -o build/2_1/nhashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nstrtabs.c -o build/2_1/nstrtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nstrtabs.c -o build/2_1/nstrtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/options.c -o build/4_1/options.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/options.c -o build/4_1/options.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/msgs.c -o build/4_1/msgs.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/msgs.c -o build/4_1/msgs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nversion.c -o build/2_1/nversion.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nversion.c -o build/2_1/nversion.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/crc.c -o build/2_1/crc.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/crc.c -o build/2_1/crc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/7_1/platform.c -o build/7_1/platform.o"
    $CC $COMP_FLAGS -Ibuild -c build/7_1/platform.c -o build/7_1/platform.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ropes.c -o build/2_1/ropes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ropes.c -o build/2_1/ropes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/idents.c -o build/2_1/idents.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/idents.c -o build/2_1/idents.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ast.c -o build/2_1/ast.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ast.c -o build/2_1/ast.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/astalgo.c -o build/2_1/astalgo.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/astalgo.c -o build/2_1/astalgo.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/condsyms.c -o build/2_1/condsyms.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/condsyms.c -o build/2_1/condsyms.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/hashes.c -o build/2_1/hashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/hashes.c -o build/2_1/hashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/strtabs.c -o build/2_1/strtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/strtabs.c -o build/2_1/strtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/streams.c -o build/2_1/streams.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/streams.c -o build/2_1/streams.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/osproc.c -o build/2_1/osproc.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/osproc.c -o build/2_1/osproc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/extccomp.c -o build/4_1/extccomp.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/extccomp.c -o build/4_1/extccomp.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/wordrecg.c -o build/2_1/wordrecg.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/wordrecg.c -o build/2_1/wordrecg.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/commands.c -o build/4_1/commands.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/commands.c -o build/4_1/commands.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/llstream.c -o build/2_1/llstream.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/llstream.c -o build/2_1/llstream.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lexbase.c -o build/2_1/lexbase.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lexbase.c -o build/2_1/lexbase.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/scanner.c -o build/2_1/scanner.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/scanner.c -o build/2_1/scanner.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/nimconf.c -o build/4_1/nimconf.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/nimconf.c -o build/4_1/nimconf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pnimsyn.c -o build/2_1/pnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pnimsyn.c -o build/2_1/pnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pbraces.c -o build/2_1/pbraces.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pbraces.c -o build/2_1/pbraces.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rnimsyn.c -o build/2_1/rnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rnimsyn.c -o build/2_1/rnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/filters.c -o build/2_1/filters.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/filters.c -o build/2_1/filters.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ptmplsyn.c -o build/2_1/ptmplsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ptmplsyn.c -o build/2_1/ptmplsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/syntaxes.c -o build/4_1/syntaxes.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/syntaxes.c -o build/4_1/syntaxes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rodread.c -o build/2_1/rodread.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rodread.c -o build/2_1/rodread.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/trees.c -o build/2_1/trees.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/trees.c -o build/2_1/trees.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/types.c -o build/2_1/types.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/types.c -o build/2_1/types.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/math.c -o build/2_1/math.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/math.c -o build/2_1/math.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/magicsys.c -o build/2_1/magicsys.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/magicsys.c -o build/2_1/magicsys.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/bitsets.c -o build/2_1/bitsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/bitsets.c -o build/2_1/bitsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nimsets.c -o build/2_1/nimsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nimsets.c -o build/2_1/nimsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/passes.c -o build/2_1/passes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/passes.c -o build/2_1/passes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/treetab.c -o build/2_1/treetab.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/treetab.c -o build/2_1/treetab.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/semdata.c -o build/2_1/semdata.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/semdata.c -o build/2_1/semdata.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lookups.c -o build/2_1/lookups.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lookups.c -o build/2_1/lookups.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/importer.c -o build/2_1/importer.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/importer.c -o build/2_1/importer.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rodwrite.c -o build/2_1/rodwrite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rodwrite.c -o build/2_1/rodwrite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/semfold.c -o build/2_1/semfold.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/semfold.c -o build/2_1/semfold.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/evals.c -o build/2_1/evals.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/evals.c -o build/2_1/evals.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/procfind.c -o build/2_1/procfind.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/procfind.c -o build/2_1/procfind.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pragmas.c -o build/2_1/pragmas.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pragmas.c -o build/2_1/pragmas.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/sem.c -o build/4_1/sem.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/sem.c -o build/4_1/sem.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rst.c -o build/2_1/rst.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rst.c -o build/2_1/rst.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/highlite.c -o build/2_1/highlite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/highlite.c -o build/2_1/highlite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/docgen.c -o build/4_1/docgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/docgen.c -o build/4_1/docgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ccgutils.c -o build/2_1/ccgutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ccgutils.c -o build/2_1/ccgutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/cgmeth.c -o build/2_1/cgmeth.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/cgmeth.c -o build/2_1/cgmeth.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/cgen.c -o build/2_1/cgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/cgen.c -o build/2_1/cgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ecmasgen.c -o build/2_1/ecmasgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ecmasgen.c -o build/2_1/ecmasgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/interact.c -o build/2_1/interact.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/interact.c -o build/2_1/interact.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/passaux.c -o build/2_1/passaux.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/passaux.c -o build/2_1/passaux.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/depends.c -o build/2_1/depends.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/depends.c -o build/2_1/depends.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/transf.c -o build/2_1/transf.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/transf.c -o build/2_1/transf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/main.c -o build/2_1/main.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/main.c -o build/2_1/main.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/parseopt.c -o build/2_1/parseopt.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/parseopt.c -o build/2_1/parseopt.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nim__dat.c -o build/2_1/nim__dat.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nim__dat.c -o build/2_1/nim__dat.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/parseutils.c -o build/2_1/parseutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/parseutils.c -o build/2_1/parseutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/strutils.c -o build/2_1/strutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/strutils.c -o build/2_1/strutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/7_1/os.c -o build/7_1/os.o"
    $CC $COMP_FLAGS -Ibuild -c build/7_1/os.c -o build/7_1/os.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/nimrod.c -o build/4_1/nimrod.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/nimrod.c -o build/4_1/nimrod.o || exit 1
    echo "$LINKER $LINK_FLAGS -o bin/nimrod  \
build/7_1/system.o \
build/2_1/times.o \
build/3_1/posix.o \
build/2_1/lists.o \
build/2_1/nhashes.o \
build/2_1/nstrtabs.o \
build/4_1/options.o \
build/4_1/msgs.o \
build/2_1/nversion.o \
build/2_1/crc.o \
build/7_1/platform.o \
build/2_1/ropes.o \
build/2_1/idents.o \
build/2_1/ast.o \
build/2_1/astalgo.o \
build/2_1/condsyms.o \
build/2_1/hashes.o \
build/2_1/strtabs.o \
build/2_1/streams.o \
build/2_1/osproc.o \
build/4_1/extccomp.o \
build/2_1/wordrecg.o \
build/4_1/commands.o \
build/2_1/llstream.o \
build/2_1/lexbase.o \
build/2_1/scanner.o \
build/4_1/nimconf.o \
build/2_1/pnimsyn.o \
build/2_1/pbraces.o \
build/2_1/rnimsyn.o \
build/2_1/filters.o \
build/2_1/ptmplsyn.o \
build/4_1/syntaxes.o \
build/2_1/rodread.o \
build/2_1/trees.o \
build/2_1/types.o \
build/2_1/math.o \
build/2_1/magicsys.o \
build/2_1/bitsets.o \
build/2_1/nimsets.o \
build/2_1/passes.o \
build/2_1/treetab.o \
build/2_1/semdata.o \
build/2_1/lookups.o \
build/2_1/importer.o \
build/2_1/rodwrite.o \
build/2_1/semfold.o \
build/2_1/evals.o \
build/2_1/procfind.o \
build/2_1/pragmas.o \
build/4_1/sem.o \
build/2_1/rst.o \
build/2_1/highlite.o \
build/4_1/docgen.o \
build/2_1/ccgutils.o \
build/2_1/cgmeth.o \
build/2_1/cgen.o \
build/2_1/ecmasgen.o \
build/2_1/interact.o \
build/2_1/passaux.o \
build/2_1/depends.o \
build/2_1/transf.o \
build/2_1/main.o \
build/2_1/parseopt.o \
build/2_1/nim__dat.o \
build/2_1/parseutils.o \
build/2_1/strutils.o \
build/7_1/os.o \
build/4_1/nimrod.o"
    $LINKER $LINK_FLAGS -o bin/nimrod  \
build/7_1/system.o \
build/2_1/times.o \
build/3_1/posix.o \
build/2_1/lists.o \
build/2_1/nhashes.o \
build/2_1/nstrtabs.o \
build/4_1/options.o \
build/4_1/msgs.o \
build/2_1/nversion.o \
build/2_1/crc.o \
build/7_1/platform.o \
build/2_1/ropes.o \
build/2_1/idents.o \
build/2_1/ast.o \
build/2_1/astalgo.o \
build/2_1/condsyms.o \
build/2_1/hashes.o \
build/2_1/strtabs.o \
build/2_1/streams.o \
build/2_1/osproc.o \
build/4_1/extccomp.o \
build/2_1/wordrecg.o \
build/4_1/commands.o \
build/2_1/llstream.o \
build/2_1/lexbase.o \
build/2_1/scanner.o \
build/4_1/nimconf.o \
build/2_1/pnimsyn.o \
build/2_1/pbraces.o \
build/2_1/rnimsyn.o \
build/2_1/filters.o \
build/2_1/ptmplsyn.o \
build/4_1/syntaxes.o \
build/2_1/rodread.o \
build/2_1/trees.o \
build/2_1/types.o \
build/2_1/math.o \
build/2_1/magicsys.o \
build/2_1/bitsets.o \
build/2_1/nimsets.o \
build/2_1/passes.o \
build/2_1/treetab.o \
build/2_1/semdata.o \
build/2_1/lookups.o \
build/2_1/importer.o \
build/2_1/rodwrite.o \
build/2_1/semfold.o \
build/2_1/evals.o \
build/2_1/procfind.o \
build/2_1/pragmas.o \
build/4_1/sem.o \
build/2_1/rst.o \
build/2_1/highlite.o \
build/4_1/docgen.o \
build/2_1/ccgutils.o \
build/2_1/cgmeth.o \
build/2_1/cgen.o \
build/2_1/ecmasgen.o \
build/2_1/interact.o \
build/2_1/passaux.o \
build/2_1/depends.o \
build/2_1/transf.o \
build/2_1/main.o \
build/2_1/parseopt.o \
build/2_1/nim__dat.o \
build/2_1/parseutils.o \
build/2_1/strutils.o \
build/7_1/os.o \
build/4_1/nimrod.o || exit 1
    ;;
  amd64)
    echo "$CC $COMP_FLAGS -Ibuild -c build/7_2/system.c -o build/7_2/system.o"
    $CC $COMP_FLAGS -Ibuild -c build/7_2/system.c -o build/7_2/system.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/times.c -o build/2_2/times.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/times.c -o build/2_2/times.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_2/posix.c -o build/3_2/posix.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_2/posix.c -o build/3_2/posix.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/lists.c -o build/2_2/lists.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/lists.c -o build/2_2/lists.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nhashes.c -o build/2_2/nhashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nhashes.c -o build/2_2/nhashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nstrtabs.c -o build/2_2/nstrtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nstrtabs.c -o build/2_2/nstrtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/options.c -o build/4_2/options.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/options.c -o build/4_2/options.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/msgs.c -o build/4_2/msgs.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/msgs.c -o build/4_2/msgs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nversion.c -o build/2_2/nversion.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nversion.c -o build/2_2/nversion.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/crc.c -o build/2_2/crc.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/crc.c -o build/2_2/crc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/7_2/platform.c -o build/7_2/platform.o"
    $CC $COMP_FLAGS -Ibuild -c build/7_2/platform.c -o build/7_2/platform.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ropes.c -o build/2_2/ropes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ropes.c -o build/2_2/ropes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/idents.c -o build/2_2/idents.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/idents.c -o build/2_2/idents.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ast.c -o build/2_2/ast.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ast.c -o build/2_2/ast.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/astalgo.c -o build/2_2/astalgo.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/astalgo.c -o build/2_2/astalgo.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/condsyms.c -o build/2_2/condsyms.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/condsyms.c -o build/2_2/condsyms.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/hashes.c -o build/2_2/hashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/hashes.c -o build/2_2/hashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/strtabs.c -o build/2_2/strtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/strtabs.c -o build/2_2/strtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/streams.c -o build/2_2/streams.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/streams.c -o build/2_2/streams.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/osproc.c -o build/2_2/osproc.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/osproc.c -o build/2_2/osproc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/extccomp.c -o build/4_2/extccomp.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/extccomp.c -o build/4_2/extccomp.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/wordrecg.c -o build/2_2/wordrecg.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/wordrecg.c -o build/2_2/wordrecg.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/commands.c -o build/4_2/commands.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/commands.c -o build/4_2/commands.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/llstream.c -o build/2_2/llstream.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/llstream.c -o build/2_2/llstream.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/lexbase.c -o build/2_2/lexbase.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/lexbase.c -o build/2_2/lexbase.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/scanner.c -o build/2_2/scanner.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/scanner.c -o build/2_2/scanner.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/nimconf.c -o build/4_2/nimconf.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/nimconf.c -o build/4_2/nimconf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/pnimsyn.c -o build/2_2/pnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/pnimsyn.c -o build/2_2/pnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/pbraces.c -o build/2_2/pbraces.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/pbraces.c -o build/2_2/pbraces.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/rnimsyn.c -o build/2_2/rnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/rnimsyn.c -o build/2_2/rnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/filters.c -o build/2_2/filters.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/filters.c -o build/2_2/filters.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ptmplsyn.c -o build/2_2/ptmplsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ptmplsyn.c -o build/2_2/ptmplsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/syntaxes.c -o build/4_2/syntaxes.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/syntaxes.c -o build/4_2/syntaxes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/rodread.c -o build/2_2/rodread.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/rodread.c -o build/2_2/rodread.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/trees.c -o build/2_2/trees.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/trees.c -o build/2_2/trees.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/types.c -o build/2_2/types.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/types.c -o build/2_2/types.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/math.c -o build/2_2/math.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/math.c -o build/2_2/math.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/magicsys.c -o build/2_2/magicsys.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/magicsys.c -o build/2_2/magicsys.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/bitsets.c -o build/2_2/bitsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/bitsets.c -o build/2_2/bitsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nimsets.c -o build/2_2/nimsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nimsets.c -o build/2_2/nimsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/passes.c -o build/2_2/passes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/passes.c -o build/2_2/passes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/treetab.c -o build/2_2/treetab.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/treetab.c -o build/2_2/treetab.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/semdata.c -o build/2_2/semdata.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/semdata.c -o build/2_2/semdata.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/lookups.c -o build/2_2/lookups.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/lookups.c -o build/2_2/lookups.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/importer.c -o build/2_2/importer.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/importer.c -o build/2_2/importer.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/rodwrite.c -o build/2_2/rodwrite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/rodwrite.c -o build/2_2/rodwrite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/semfold.c -o build/2_2/semfold.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/semfold.c -o build/2_2/semfold.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/evals.c -o build/2_2/evals.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/evals.c -o build/2_2/evals.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/procfind.c -o build/2_2/procfind.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/procfind.c -o build/2_2/procfind.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/pragmas.c -o build/2_2/pragmas.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/pragmas.c -o build/2_2/pragmas.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/sem.c -o build/4_2/sem.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/sem.c -o build/4_2/sem.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/rst.c -o build/2_2/rst.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/rst.c -o build/2_2/rst.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/highlite.c -o build/2_2/highlite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/highlite.c -o build/2_2/highlite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/docgen.c -o build/4_2/docgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/docgen.c -o build/4_2/docgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ccgutils.c -o build/2_2/ccgutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ccgutils.c -o build/2_2/ccgutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/cgmeth.c -o build/2_2/cgmeth.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/cgmeth.c -o build/2_2/cgmeth.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/cgen.c -o build/2_2/cgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/cgen.c -o build/2_2/cgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/ecmasgen.c -o build/2_2/ecmasgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/ecmasgen.c -o build/2_2/ecmasgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/interact.c -o build/2_2/interact.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/interact.c -o build/2_2/interact.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/passaux.c -o build/2_2/passaux.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/passaux.c -o build/2_2/passaux.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/depends.c -o build/2_2/depends.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/depends.c -o build/2_2/depends.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/transf.c -o build/2_2/transf.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/transf.c -o build/2_2/transf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/main.c -o build/2_2/main.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/main.c -o build/2_2/main.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/parseopt.c -o build/2_2/parseopt.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/parseopt.c -o build/2_2/parseopt.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/nim__dat.c -o build/2_2/nim__dat.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/nim__dat.c -o build/2_2/nim__dat.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/parseutils.c -o build/2_2/parseutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/parseutils.c -o build/2_2/parseutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_2/strutils.c -o build/2_2/strutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_2/strutils.c -o build/2_2/strutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/7_2/os.c -o build/7_2/os.o"
    $CC $COMP_FLAGS -Ibuild -c build/7_2/os.c -o build/7_2/os.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_2/nimrod.c -o build/4_2/nimrod.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_2/nimrod.c -o build/4_2/nimrod.o || exit 1
    echo "$LINKER $LINK_FLAGS -o bin/nimrod  \
build/7_2/system.o \
build/2_2/times.o \
build/3_2/posix.o \
build/2_2/lists.o \
build/2_2/nhashes.o \
build/2_2/nstrtabs.o \
build/4_2/options.o \
build/4_2/msgs.o \
build/2_2/nversion.o \
build/2_2/crc.o \
build/7_2/platform.o \
build/2_2/ropes.o \
build/2_2/idents.o \
build/2_2/ast.o \
build/2_2/astalgo.o \
build/2_2/condsyms.o \
build/2_2/hashes.o \
build/2_2/strtabs.o \
build/2_2/streams.o \
build/2_2/osproc.o \
build/4_2/extccomp.o \
build/2_2/wordrecg.o \
build/4_2/commands.o \
build/2_2/llstream.o \
build/2_2/lexbase.o \
build/2_2/scanner.o \
build/4_2/nimconf.o \
build/2_2/pnimsyn.o \
build/2_2/pbraces.o \
build/2_2/rnimsyn.o \
build/2_2/filters.o \
build/2_2/ptmplsyn.o \
build/4_2/syntaxes.o \
build/2_2/rodread.o \
build/2_2/trees.o \
build/2_2/types.o \
build/2_2/math.o \
build/2_2/magicsys.o \
build/2_2/bitsets.o \
build/2_2/nimsets.o \
build/2_2/passes.o \
build/2_2/treetab.o \
build/2_2/semdata.o \
build/2_2/lookups.o \
build/2_2/importer.o \
build/2_2/rodwrite.o \
build/2_2/semfold.o \
build/2_2/evals.o \
build/2_2/procfind.o \
build/2_2/pragmas.o \
build/4_2/sem.o \
build/2_2/rst.o \
build/2_2/highlite.o \
build/4_2/docgen.o \
build/2_2/ccgutils.o \
build/2_2/cgmeth.o \
build/2_2/cgen.o \
build/2_2/ecmasgen.o \
build/2_2/interact.o \
build/2_2/passaux.o \
build/2_2/depends.o \
build/2_2/transf.o \
build/2_2/main.o \
build/2_2/parseopt.o \
build/2_2/nim__dat.o \
build/2_2/parseutils.o \
build/2_2/strutils.o \
build/7_2/os.o \
build/4_2/nimrod.o"
    $LINKER $LINK_FLAGS -o bin/nimrod  \
build/7_2/system.o \
build/2_2/times.o \
build/3_2/posix.o \
build/2_2/lists.o \
build/2_2/nhashes.o \
build/2_2/nstrtabs.o \
build/4_2/options.o \
build/4_2/msgs.o \
build/2_2/nversion.o \
build/2_2/crc.o \
build/7_2/platform.o \
build/2_2/ropes.o \
build/2_2/idents.o \
build/2_2/ast.o \
build/2_2/astalgo.o \
build/2_2/condsyms.o \
build/2_2/hashes.o \
build/2_2/strtabs.o \
build/2_2/streams.o \
build/2_2/osproc.o \
build/4_2/extccomp.o \
build/2_2/wordrecg.o \
build/4_2/commands.o \
build/2_2/llstream.o \
build/2_2/lexbase.o \
build/2_2/scanner.o \
build/4_2/nimconf.o \
build/2_2/pnimsyn.o \
build/2_2/pbraces.o \
build/2_2/rnimsyn.o \
build/2_2/filters.o \
build/2_2/ptmplsyn.o \
build/4_2/syntaxes.o \
build/2_2/rodread.o \
build/2_2/trees.o \
build/2_2/types.o \
build/2_2/math.o \
build/2_2/magicsys.o \
build/2_2/bitsets.o \
build/2_2/nimsets.o \
build/2_2/passes.o \
build/2_2/treetab.o \
build/2_2/semdata.o \
build/2_2/lookups.o \
build/2_2/importer.o \
build/2_2/rodwrite.o \
build/2_2/semfold.o \
build/2_2/evals.o \
build/2_2/procfind.o \
build/2_2/pragmas.o \
build/4_2/sem.o \
build/2_2/rst.o \
build/2_2/highlite.o \
build/4_2/docgen.o \
build/2_2/ccgutils.o \
build/2_2/cgmeth.o \
build/2_2/cgen.o \
build/2_2/ecmasgen.o \
build/2_2/interact.o \
build/2_2/passaux.o \
build/2_2/depends.o \
build/2_2/transf.o \
build/2_2/main.o \
build/2_2/parseopt.o \
build/2_2/nim__dat.o \
build/2_2/parseutils.o \
build/2_2/strutils.o \
build/7_2/os.o \
build/4_2/nimrod.o || exit 1
    ;;
  powerpc)
    echo "$CC $COMP_FLAGS -Ibuild -c build/7_1/system.c -o build/7_1/system.o"
    $CC $COMP_FLAGS -Ibuild -c build/7_1/system.c -o build/7_1/system.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/times.c -o build/2_1/times.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/times.c -o build/2_1/times.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/3_1/posix.c -o build/3_1/posix.o"
    $CC $COMP_FLAGS -Ibuild -c build/3_1/posix.c -o build/3_1/posix.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lists.c -o build/2_1/lists.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lists.c -o build/2_1/lists.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nhashes.c -o build/2_1/nhashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nhashes.c -o build/2_1/nhashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nstrtabs.c -o build/2_1/nstrtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nstrtabs.c -o build/2_1/nstrtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/options.c -o build/4_3/options.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/options.c -o build/4_3/options.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/msgs.c -o build/4_3/msgs.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/msgs.c -o build/4_3/msgs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nversion.c -o build/2_1/nversion.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nversion.c -o build/2_1/nversion.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/crc.c -o build/2_1/crc.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/crc.c -o build/2_1/crc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/7_3/platform.c -o build/7_3/platform.o"
    $CC $COMP_FLAGS -Ibuild -c build/7_3/platform.c -o build/7_3/platform.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ropes.c -o build/2_1/ropes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ropes.c -o build/2_1/ropes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/idents.c -o build/2_1/idents.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/idents.c -o build/2_1/idents.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/ast.c -o build/2_3/ast.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/ast.c -o build/2_3/ast.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/astalgo.c -o build/2_1/astalgo.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/astalgo.c -o build/2_1/astalgo.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/condsyms.c -o build/2_1/condsyms.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/condsyms.c -o build/2_1/condsyms.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/hashes.c -o build/2_1/hashes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/hashes.c -o build/2_1/hashes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/strtabs.c -o build/2_1/strtabs.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/strtabs.c -o build/2_1/strtabs.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/streams.c -o build/2_1/streams.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/streams.c -o build/2_1/streams.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/osproc.c -o build/2_1/osproc.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/osproc.c -o build/2_1/osproc.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/extccomp.c -o build/4_3/extccomp.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/extccomp.c -o build/4_3/extccomp.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/wordrecg.c -o build/2_1/wordrecg.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/wordrecg.c -o build/2_1/wordrecg.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/commands.c -o build/4_3/commands.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/commands.c -o build/4_3/commands.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/llstream.c -o build/2_1/llstream.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/llstream.c -o build/2_1/llstream.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/lexbase.c -o build/2_1/lexbase.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/lexbase.c -o build/2_1/lexbase.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/scanner.c -o build/2_1/scanner.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/scanner.c -o build/2_1/scanner.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/nimconf.c -o build/4_1/nimconf.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/nimconf.c -o build/4_1/nimconf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pnimsyn.c -o build/2_1/pnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pnimsyn.c -o build/2_1/pnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/pbraces.c -o build/2_1/pbraces.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/pbraces.c -o build/2_1/pbraces.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rnimsyn.c -o build/2_1/rnimsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rnimsyn.c -o build/2_1/rnimsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/filters.c -o build/2_1/filters.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/filters.c -o build/2_1/filters.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ptmplsyn.c -o build/2_1/ptmplsyn.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ptmplsyn.c -o build/2_1/ptmplsyn.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/syntaxes.c -o build/4_1/syntaxes.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/syntaxes.c -o build/4_1/syntaxes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rodread.c -o build/2_1/rodread.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rodread.c -o build/2_1/rodread.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/trees.c -o build/2_1/trees.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/trees.c -o build/2_1/trees.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/types.c -o build/2_3/types.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/types.c -o build/2_3/types.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/math.c -o build/2_1/math.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/math.c -o build/2_1/math.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/magicsys.c -o build/2_1/magicsys.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/magicsys.c -o build/2_1/magicsys.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/bitsets.c -o build/2_1/bitsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/bitsets.c -o build/2_1/bitsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nimsets.c -o build/2_1/nimsets.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nimsets.c -o build/2_1/nimsets.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/passes.c -o build/2_3/passes.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/passes.c -o build/2_3/passes.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/treetab.c -o build/2_1/treetab.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/treetab.c -o build/2_1/treetab.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/semdata.c -o build/2_1/semdata.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/semdata.c -o build/2_1/semdata.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/lookups.c -o build/2_3/lookups.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/lookups.c -o build/2_3/lookups.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/importer.c -o build/2_3/importer.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/importer.c -o build/2_3/importer.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/rodwrite.c -o build/2_3/rodwrite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/rodwrite.c -o build/2_3/rodwrite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/semfold.c -o build/2_3/semfold.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/semfold.c -o build/2_3/semfold.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/evals.c -o build/2_3/evals.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/evals.c -o build/2_3/evals.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/procfind.c -o build/2_1/procfind.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/procfind.c -o build/2_1/procfind.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/pragmas.c -o build/2_3/pragmas.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/pragmas.c -o build/2_3/pragmas.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/sem.c -o build/4_3/sem.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/sem.c -o build/4_3/sem.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/rst.c -o build/2_1/rst.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/rst.c -o build/2_1/rst.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/highlite.c -o build/2_1/highlite.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/highlite.c -o build/2_1/highlite.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_1/docgen.c -o build/4_1/docgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_1/docgen.c -o build/4_1/docgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/ccgutils.c -o build/2_1/ccgutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/ccgutils.c -o build/2_1/ccgutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/cgmeth.c -o build/2_3/cgmeth.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/cgmeth.c -o build/2_3/cgmeth.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/cgen.c -o build/2_3/cgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/cgen.c -o build/2_3/cgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/ecmasgen.c -o build/2_3/ecmasgen.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/ecmasgen.c -o build/2_3/ecmasgen.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/interact.c -o build/2_1/interact.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/interact.c -o build/2_1/interact.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/passaux.c -o build/2_1/passaux.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/passaux.c -o build/2_1/passaux.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/depends.c -o build/2_1/depends.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/depends.c -o build/2_1/depends.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_3/transf.c -o build/2_3/transf.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_3/transf.c -o build/2_3/transf.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/main.c -o build/2_1/main.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/main.c -o build/2_1/main.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/parseopt.c -o build/2_1/parseopt.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/parseopt.c -o build/2_1/parseopt.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/nim__dat.c -o build/2_1/nim__dat.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/nim__dat.c -o build/2_1/nim__dat.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/parseutils.c -o build/2_1/parseutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/parseutils.c -o build/2_1/parseutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/2_1/strutils.c -o build/2_1/strutils.o"
    $CC $COMP_FLAGS -Ibuild -c build/2_1/strutils.c -o build/2_1/strutils.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/7_1/os.c -o build/7_1/os.o"
    $CC $COMP_FLAGS -Ibuild -c build/7_1/os.c -o build/7_1/os.o || exit 1
    echo "$CC $COMP_FLAGS -Ibuild -c build/4_3/nimrod.c -o build/4_3/nimrod.o"
    $CC $COMP_FLAGS -Ibuild -c build/4_3/nimrod.c -o build/4_3/nimrod.o || exit 1
    echo "$LINKER $LINK_FLAGS -o bin/nimrod  \
build/7_1/system.o \
build/2_1/times.o \
build/3_1/posix.o \
build/2_1/lists.o \
build/2_1/nhashes.o \
build/2_1/nstrtabs.o \
build/4_3/options.o \
build/4_3/msgs.o \
build/2_1/nversion.o \
build/2_1/crc.o \
build/7_3/platform.o \
build/2_1/ropes.o \
build/2_1/idents.o \
build/2_3/ast.o \
build/2_1/astalgo.o \
build/2_1/condsyms.o \
build/2_1/hashes.o \
build/2_1/strtabs.o \
build/2_1/streams.o \
build/2_1/osproc.o \
build/4_3/extccomp.o \
build/2_1/wordrecg.o \
build/4_3/commands.o \
build/2_1/llstream.o \
build/2_1/lexbase.o \
build/2_1/scanner.o \
build/4_1/nimconf.o \
build/2_1/pnimsyn.o \
build/2_1/pbraces.o \
build/2_1/rnimsyn.o \
build/2_1/filters.o \
build/2_1/ptmplsyn.o \
build/4_1/syntaxes.o \
build/2_1/rodread.o \
build/2_1/trees.o \
build/2_3/types.o \
build/2_1/math.o \
build/2_1/magicsys.o \
build/2_1/bitsets.o \
build/2_1/nimsets.o \
build/2_3/passes.o \
build/2_1/treetab.o \
build/2_1/semdata.o \
build/2_3/lookups.o \
build/2_3/importer.o \
build/2_3/rodwrite.o \
build/2_3/semfold.o \
build/2_3/evals.o \
build/2_1/procfind.o \
build/2_3/pragmas.o \
build/4_3/sem.o \
build/2_1/rst.o \
build/2_1/highlite.o \
build/4_1/docgen.o \
build/2_1/ccgutils.o \
build/2_3/cgmeth.o \
build/2_3/cgen.o \
build/2_3/ecmasgen.o \
build/2_1/interact.o \
build/2_1/passaux.o \
build/2_1/depends.o \
build/2_3/transf.o \
build/2_1/main.o \
build/2_1/parseopt.o \
build/2_1/nim__dat.o \
build/2_1/parseutils.o \
build/2_1/strutils.o \
build/7_1/os.o \
build/4_3/nimrod.o"
    $LINKER $LINK_FLAGS -o bin/nimrod  \
build/7_1/system.o \
build/2_1/times.o \
build/3_1/posix.o \
build/2_1/lists.o \
build/2_1/nhashes.o \
build/2_1/nstrtabs.o \
build/4_3/options.o \
build/4_3/msgs.o \
build/2_1/nversion.o \
build/2_1/crc.o \
build/7_3/platform.o \
build/2_1/ropes.o \
build/2_1/idents.o \
build/2_3/ast.o \
build/2_1/astalgo.o \
build/2_1/condsyms.o \
build/2_1/hashes.o \
build/2_1/strtabs.o \
build/2_1/streams.o \
build/2_1/osproc.o \
build/4_3/extccomp.o \
build/2_1/wordrecg.o \
build/4_3/commands.o \
build/2_1/llstream.o \
build/2_1/lexbase.o \
build/2_1/scanner.o \
build/4_1/nimconf.o \
build/2_1/pnimsyn.o \
build/2_1/pbraces.o \
build/2_1/rnimsyn.o \
build/2_1/filters.o \
build/2_1/ptmplsyn.o \
build/4_1/syntaxes.o \
build/2_1/rodread.o \
build/2_1/trees.o \
build/2_3/types.o \
build/2_1/math.o \
build/2_1/magicsys.o \
build/2_1/bitsets.o \
build/2_1/nimsets.o \
build/2_3/passes.o \
build/2_1/treetab.o \
build/2_1/semdata.o \
build/2_3/lookups.o \
build/2_3/importer.o \
build/2_3/rodwrite.o \
build/2_3/semfold.o \
build/2_3/evals.o \
build/2_1/procfind.o \
build/2_3/pragmas.o \
build/4_3/sem.o \
build/2_1/rst.o \
build/2_1/highlite.o \
build/4_1/docgen.o \
build/2_1/ccgutils.o \
build/2_3/cgmeth.o \
build/2_3/cgen.o \
build/2_3/ecmasgen.o \
build/2_1/interact.o \
build/2_1/passaux.o \
build/2_1/depends.o \
build/2_3/transf.o \
build/2_1/main.o \
build/2_1/parseopt.o \
build/2_1/nim__dat.o \
build/2_1/parseutils.o \
build/2_1/strutils.o \
build/7_1/os.o \
build/4_3/nimrod.o || exit 1
    ;;
  *)
    echo "Error: no C code generated for: [$myos: $mycpu]"
    exit 1
    ;;
  esac
  ;;
*) 
  echo "Error: no C code generated for: [$myos: $mycpu]"
  exit 1
  ;;
esac

echo "SUCCESS"

