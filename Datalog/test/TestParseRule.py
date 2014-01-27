'''
Created on 31 Jul 2013

@author: nando
'''
import unittest
from BuildRulesTable import parseRule

class TestParsing(unittest.TestCase):
    
    def executeTestResultsMustBeEqual(self, rule, good_result, obtained_result):
        ErrorMessage = "Error parsing rule: " + rule + \
                        "\nObtained Result: " + str(parseRule(rule)) + \
                        "\nExpected Result: " + str(good_result) 
        self.assertEqual(obtained_result, good_result, ErrorMessage)
        
    def testparseRule_1HypotesisRule(self):
        rule = 'A(X, Z) :- B(X, Z).'
        good_result = (('A', ['X', 'Z']), [('B', ['X', 'Z'])])
        obtained_result = parseRule(rule)
        self.executeTestResultsMustBeEqual(rule, good_result, obtained_result)
        
    def testparseRule_1HypotesisRuleNoSpaces(self):
        rule = 'A(X,Z):-B(X,Z).'
        good_result = (('A', ['X', 'Z']), [('B', ['X', 'Z'])])
        obtained_result = parseRule(rule)
        self.executeTestResultsMustBeEqual(rule, good_result, obtained_result)
        
    def testparseRule_1HypotesisRuleRandomSpaces(self):
        rule = 'A(X,          Z)    :-             B(X,                Z).'
        good_result = (('A', ['X', 'Z']), [('B', ['X', 'Z'])])
        obtained_result = parseRule(rule)
        self.executeTestResultsMustBeEqual(rule, good_result, obtained_result)
        
    # May be this should be considered an error?
    def testparseRule_1HypotesisRuleSaceinRuleSeparator(self):
        rule = 'A(X, Z) :    - B(X, Z).'
        good_result = (('A', ['X', 'Z']), [('B', ['X', 'Z'])])
        obtained_result = parseRule(rule)
        self.executeTestResultsMustBeEqual(rule, good_result, obtained_result)
        
    def testparseRule_1HypotesisLongNamesRadomSpaces(self):
        rule = 'ThisIsALongName(      LongLongName1  , LongLongLongName2) :    - AnotherLongName(LongLongName3, LongLongLongName4).'
        good_result = (('ThisIsALongName', ['LongLongName1', 'LongLongLongName2']), 
                    [('AnotherLongName', ['LongLongName3', 'LongLongLongName4'])])
        obtained_result = parseRule(rule)
        self.executeTestResultsMustBeEqual(rule, good_result, obtained_result)
        
    # May be this also should fail, this fails now
    def testparseRule_1HypotesisRuleNoFinalDot(self):
        rule = 'A(X,Z):-B(X,Z)'
        #good_result = (('A', ['X', 'Z']), [('B', ['X', 'Z'])])
        #obtained_result = parseRule(rule)
        #self.executeTestResultsMustBeEqual(rule, good_result, obtained_result)
        try:
            parseRule(rule)
        except ValueError: pass
        else:
            self.fail("Invalid Rule: " + rule  + " should have raised an exception")
        
    def testparseRule_2HypotesisRule(self):
        rule = 'A(X, Y) :- B(X, Z), C(Z, Y).'
        good_result = (('A', ['X', 'Y']), [('B', ['X', 'Z']), ('C', ['Z', 'Y'])])
        obtained_result = parseRule(rule)
        self.executeTestResultsMustBeEqual(rule, good_result, obtained_result)
        
    def testparseRule_2HypotesisRuleNoSpaces(self):
        rule = 'A(X,Y):-B(X,Z),C(Z,Y).'
        good_result = (('A', ['X', 'Y']), [('B', ['X', 'Z']), ('C', ['Z', 'Y'])])
        obtained_result = parseRule(rule)
        self.executeTestResultsMustBeEqual(rule, good_result, obtained_result)
        
    def testparseRule_2HypotesisRuleRandomSpaces(self):
        rule = 'A(X,          Y) :-              B(          X, Z), C(     Z, Y)     .'
        good_result = (('A', ['X', 'Y']), [('B', ['X', 'Z']), ('C', ['Z', 'Y'])])
        obtained_result = parseRule(rule)
        self.executeTestResultsMustBeEqual(rule, good_result, obtained_result)
        
    # May be these also should fail, these fail now
    def testparseRule_2HypotesisRuleNoFinalDot(self):
        rule = 'A(X, Y) :- B(X, Z), C(Z, Y)'
        #good_result = (('A', ['X', 'Y']), [('B', ['X', 'Z']), ('C', ['Z', 'Y'])])
        #obtained_result = parseRule(rule)
        #self.executeTestResultsMustBeEqual(rule, good_result, obtained_result)
        try:
            parseRule(rule)
        except ValueError: pass
        else:
            self.fail("Invalid Rule: " + rule  + " should have raised an exception")
        
    def testparseRule_3HypotesisRule(self):
        rule = 'A(X, W) :- B(X, Z), C(Z, Y), D(Z, W).'
        #good_result = (('A', ['X', 'W']), [('B', ['X', 'Z']), ('C', ['Z', 'Y']), ('D', ['Z', 'W'])])
        #obtained_result = parseRule(rule)
        #self.executeTestResultsMustBeEqual(rule, good_result, obtained_result)
        try:
            parseRule(rule)
        except ValueError: pass
        else:
            self.fail("Invalid Rule: " + rule  + " should have raised an exception")
        
    def testparseRule_3HypotesisRuleRandomSpaces(self):
        rule = 'A          (X, W) :- B(      X, Z), C(Z           , Y), D(  Z, W).'
        #good_result = (('A', ['X', 'W']), [('B', ['X', 'Z']), ('C', ['Z', 'Y']), ('D', ['Z', 'W'])])
        #obtained_result = parseRule(rule)
        #self.executeTestResultsMustBeEqual(rule, good_result, obtained_result)
        try:
            parseRule(rule)
        except ValueError: pass
        else:
            self.fail("Invalid Rule: " + rule  + " should have raised an exception")
        
    # Errors
    def testparseRuleMalformedRuleNoHeadRule(self):
        rule = 'A(X, Z) B(X, Z).'
        try:
            parseRule(rule)
        except ValueError: pass
        else:
            self.fail("Invalid Rule: " + rule  + " should have raised an exception")
            
    def testparseRuleMalformedRuleNoBodySeparator(self):
        rule = 'A(X, Y) :- B(X, Z) C(Z, Y).'
        try:
            parseRule(rule)
        except ValueError: pass
        else:
            self.fail("Invalid Rule: " + rule  + " should have raised an exception")
            
    def testparseRuleMalformedRuleMissingClosingParentesis(self):
        rule = 'A(X, Y) :- B(X, Z, C(Z, Y).'
        try:
            parseRule(rule)
        except ValueError: pass
        else:
            self.fail("Invalid Rule: " + rule  + " should have raised an exception")
            
    def testparseRuleMalformedRuleMissingOpeningParentesis(self):
        rule = 'A(X, Y) :- B(X, Z), CZ, Y).'
        try:
            parseRule(rule)
        except ValueError: pass
        else:
            self.fail("Invalid Rule: " + rule  + " should have raised an exception")
        
if __name__ == "__main__":
    #import sys;sys.argv = ['', 'Test.testName']
    unittest.main()