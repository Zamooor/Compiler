Comments:

    When in the INITIAL state if a /* is found we transition into the COMMENT state, and increase a nesting counter.  Then, when in the COMMENT state, if we find another /* we increment the counter again.  Then we ignore all inputs until we see a */, if nesting is 0 we return to the INITIAL state, otherwise we decrement the counter and continue in the COMMENT state.
    
Strings:

    When we see a " from the INITIAL state we enter the STRING state.  Until we see the matching closing " we remain in the STRING state.  All of the described escape sequences (from the Appendix) have unique rules that will replace them with their translations, so "\n" will result in a new line and \^c will result in a . We know that the translations are correct because you can copy the box characters and paste them into the command line and get the same effect as if you had manualy hit the corresponding ctrl command. One improvement that could be made is when there are new lines in \f...f\ the lineNum reference isn't incremented so later errors in the tig file don't have the correct line numbers.  We will have to add another state to deal with this.  
    
Error handling:

    For error handling we use the givven ErrorMsg.error function.  Again, because of the \f...f\ newline problem, described in strings above, the reports aren't accurate.  
    
end-of-file hadnling:
    
    We use the given eof function modified to additionaly display an error if there is an unclosed comment or string.
    
Other interesting features:
    We couldn't get the method you described (ord(c)-ord(a)+1) to work so we explicitly handle each of the following control sequences
    \^[a-zA-Z] \^\ \^[ \^] \^^ \^_ \^@
    
    It should also be noted that codes above \255 correctly result in error messages, while codes above 176 just print out their escape sequence and not there value like the lower codes do. This behavior is odd because all codes between 0 and 255 should be handled by the same rule.
