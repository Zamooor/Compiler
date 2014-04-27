CM.make "sources.cm";

PrintAbsyn.print(TextIO.openOut "output.txt" , Parse.parse ("testfiles/queens.tig"));


OS.Process.exit(OS.Process.success);
