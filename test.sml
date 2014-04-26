CM.make "sources.cm";

PrintAbsyn.print(TextIO.openOut "output.txt" , Parse.parse ("testfiles/test3.tig"));

OS.Process.exit(OS.Process.success);
