CM.make "sources.cm";

PrintAbsyn.print(TextIO.stdOut , Parse.parse ("test.tig"));


OS.Process.exit(OS.Process.success);
