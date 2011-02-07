Macaulay2, version 1.3.1.1
with packages: ConwayPolynomials, Elimination, IntegralClosure, 
               LLLBases, PrimaryDecomposition, ReesAlgebra, SchurRings, TangentCone

i3 : f = method()

o3 = f

o3 : MethodFunction

i4 : f Sequence := identity

o4 = identity

o4 : CompiledFunction

i5 : f(a,b,c)
stdio:6:1:(3): error: no method found for applying f to:
     argument 1 :  a (of class Symbol)
     argument 2 :  b (of class Symbol)
     argument 3 :  c (of class Symbol)

i6 : f((a,b,c))
stdio:7:1:(3): error: no method found for applying f to:
     argument 1 :  a (of class Symbol)
     argument 2 :  b (of class Symbol)
     argument 3 :  c (of class Symbol)

i7 : 1:3

o7 = 1 : (3)

o7 : Sequence

i8 : options method

o8 = OptionTable{Binary => false                         }
                 Dispatch => {Thing, Thing, Thing, Thing}
                 Options => null
                 TypicalValue => Thing

o8 : OptionTable

i9 : g = method(Dispatch=>Thing)

o9 = g

o9 : CompiledFunctionClosure

i10 : g Sequence := identity

o10 = identity

o10 : CompiledFunction

i11 : g(a,b,c)

o11 = (a, b, c)

o11 : Sequence

i12 : f(a,b,c,d)
stdio:13:1:(3): error: no method found for applying f to:
     argument 1 :  a (of class Symbol)
     argument 2 :  b (of class Symbol)
     argument 3 :  c (of class Symbol)
     argument 4 :  d (of class Symbol)

i13 : f(a,b,c,d,e)
stdio:14:1:(3): error: no method found for applying f to:
     argument   :  (a, b, c, d, e) (of class Sequence)

i14 : options method

o14 = OptionTable{Binary => false                         }
                  Dispatch => {Thing, Thing, Thing, Thing}
                  Options => null
                  TypicalValue => Thing

o14 : OptionTable

i15 : g)
stdio:16:2:(3): error: syntax error: unmatched )

i16 : g()

o16 = ()

o16 : Sequence

i17 : g(1:2)

o17 = 1 : (2)

o17 : Sequence

i18 : g = method(Dispatch=>{Thing,Type})
--warning: function g redefined

o18 = g

o18 : MethodFunction

i19 : g(a,b)
stdio:20:1:(3): error: g: expected argument 2 to be a type, but it was: b

i20 : g(a,ZZ)
stdio:21:1:(3): error: no method found for applying g to:
     argument 1 :  a (of class Symbol)
     argument 2 :  ZZ

i21 : g(a,b,c)
stdio:22:1:(3): error: g: expected argument 2 to be a type, but it was: b

i22 : g(a,ZZ,c)
stdio:23:1:(3): error: no method found for applying g to:
     argument 1 :  a (of class Symbol)
     argument 2 :  ZZ
     argument 3 :  c (of class Symbol)

i23 : options method

o23 = OptionTable{Binary => false                         }
                  Dispatch => {Thing, Thing, Thing, Thing}
                  Options => null
                  TypicalValue => Thing

o23 : OptionTable

i24 : h = (a,b) -> a+b

o24 = h

o24 : FunctionClosure

i25 : h 1
stdio:25:11:(3): error: expected 2 arguments but got 1

i26 : h = (a) -> -a
--warning: function h redefined

o26 = h

o26 : FunctionClosure

i27 : h 1

o27 = -1

i28 : h(2,3)
stdio:27:9:(3): error: expected 1 argument, but got 2

i29 : h = a -> {3:a}
--warning: function h redefined

o29 = h

o29 : FunctionClosure

i30 : h(2,3)

o30 = {((2, 3), (2, 3), (2, 3))}

o30 : List

i31 : options method

o31 = OptionTable{Binary => false                         }
                  Dispatch => {Thing, Thing, Thing, Thing}
                  Options => null
                  TypicalValue => Thing

o31 : OptionTable

i32 : p = method(Options => {A => 1, B => 2})

o32 = p

o32 : MethodFunctionWithOptions

i33 : p ZZ := identity

o33 = identity

o33 : CompiledFunction

i34 : p 3
stdio:35:1:(3): error: expected a function

i35 : p ZZ := opt -> x -> (opt,x)

o35 = {*Function[stdio:36:12-36:25]*}

o35 : FunctionClosure

i36 : p 3

o36 = (OptionTable{A => 1}, 3)
                   B => 2

o36 : Sequence

i37 : p (3, B=>333)

o37 = (OptionTable{A => 1  }, 3)
                   B => 333

o37 : Sequence

i38 : options installPackage 

o38 = OptionTable{AbsoluteLinks => true                                               }
                  CacheExampleOutput => false
                  CheckDocumentation => true
                  DebuggingMode => false
                  Encapsulate => false
                  EncapsulateDirectory => {*Function[../../m2/html.m2:578:38-578:76]*}
                  FileName => null
                  IgnoreExampleErrors => false
                  InstallPrefix => {*Function[../../m2/html.m2:575:30-575:56]*}
                  MakeDocumentation => true
                  MakeInfo => true
                  MakeLinks => true
                  PackagePrefix => {*Function[../../m2/html.m2:574:30-574:56]*}
                  RemakeAllDocumentation => true
                  RerunExamples => false
                  RunExamples => true
                  SeparateExec => false
                  UserMode => null
                  Verbose => true

o38 : OptionTable

i39 : methods p

o39 = {(p, ZZ)}

o39 : VerticalList

i40 : methods h

o40 = {}

o40 : VerticalList

i41 : methods g

o41 = {}

o41 : VerticalList

i42 : methods g

o42 = {}

o42 : VerticalList

i43 : methods f

o43 = {(f, Sequence)}

o43 : VerticalList

i44 : t = method()

o44 = t

o44 : MethodFunction

i45 : t VisibleList := identity

o45 = identity

o45 : CompiledFunction

i46 : t {}

o46 = {}

o46 : List

i47 : t ()
stdio:48:1:(3): error: no method found for applying t to:
     argument   :  () (of class Sequence)

i48 : t = method(Dispatch=>Thing)
--warning: function t redefined

o48 = t

o48 : CompiledFunctionClosure

i49 : t VisibleList := identity

o49 = identity

o49 : CompiledFunction

i50 : t ()

o50 = ()

o50 : Sequence

i51 : t {}

o51 = {}

o51 : List

i52 : showStructure 

o52 = Thing : BasicList : Command
                          Constant
                          DocumentTag
                          Eliminate
                          Expression : Adjacent
                                       AssociativeExpression : Equation
                                                               Product
                                                               Sum
                                       BinaryOperation
                                       Divide
                                       FunctionApplication
                                       Holder : OneExpression
                                                ZeroExpression
                                       MatrixExpression
                                       Minus
                                       NonAssociativeProduct
                                       Parenthesize
                                       Power
                                       RowExpression
                                       SparseMonomialVectorExpression
                                       SparseVectorExpression
                                       Subscript
                                       Superscript
                                       Table
                          FilePosition
                          ForestNode
                          Hybrid
                          IndeterminateNumber
                          IndexedVariable
                          InfiniteNumber
                          LowerBound
                          Manipulator
                          MutableList : Bag
                          Option
                          Partition
                          ProductOrder
                          PushforwardComputation
                          RingElement
                          SumOfTwists
                          Time
                          TreeNode
                          URL
                          Vector
                          VisibleList : Array
                                        List : VerticalList
                                        Sequence
              Boolean
              CompiledFunctionBody
              Database
              Dictionary : GlobalDictionary
                           LocalDictionary
              File
              Function : CompiledFunction
                         CompiledFunctionClosure : MethodFunction
                         FunctionClosure : CacheFunction
                                           MethodFunctionWithOptions
              FunctionBody
              HashTable : CoherentSheaf
                          Ideal : MonomialIdeal
                          ImmutableType : Module
                          ModuleMap : Matrix
                          MonoidElement
                          MutableHashTable : CacheTable
                                             Descent
                                             GradedModule : ChainComplex
                                             GradedModuleMap : ChainComplexMap
                                             GroebnerBasis
                                             IndexedVariableTable : SchurRingIndexedVariableTable
                                             Package
                                             Resolution
                                             ScriptedFunctor
                                             Type : HeaderType
                                                    Monoid : OrderedMonoid : GeneralOrderedMonoid
                                                    Ring : EngineRing : FractionField
                                                                        GaloisField
                                                                        InexactField : ComplexField
                                                                                       RealField
                                                                        PolynomialRing
                                                                        QuotientRing
                                                                        SchurRing
                                                    RingFamily : InexactFieldFamily
                                                    SelfInitializingType
                                                    WrapperType
                                             Variety : AffineVariety
                                                       ProjectiveVariety
                          MutableMatrix
                          OptionTable : GroebnerBasisOptions
                          ProjectiveHilbertPolynomial
                          RingMap
                          SheafOfRings
                          Tally : Set
                                  VirtualTally : BettiTally
              LibxmlAttribute
              LibxmlNode
              Net : String
              NetFile
              Nothing : InexactNumber
                                     *
              Number : InexactNumber : CC
                                       RR
                       QQ
                       ZZ
              Pseudocode
              Symbol : Keyword
              Thread

o52 : Descent

i53 : VerticalList {a,b,c}

o53 = {a}
      {b}
      {c}

o53 : VerticalList

i54 : oo#1

o54 = b

o54 : Symbol

i55 : partitions 3

o55 = {Partition{3}, Partition{2, 1}, Partition{1, 1, 1}}

o55 : List

i56 : oo#1

o56 = Partition{2, 1}

o56 : Partition

i57 : class oo

o57 = Partition

o57 : Type

i58 : ancestors oo

o58 = {Partition, BasicList, Thing}

o58 : List

i60 : o56_1

o60 = 1

i61 : methods Partition

o61 = {(_, Partition, ZZ)    }
      {(conjugate, Partition)}

o61 : VerticalList

i62 : methods VisibleList

o62 = {(/, VisibleList, Command)                                       }
      {(/, VisibleList, Function)                                      }
      {(/, VisibleList, SelfInitializingType)                          }
      {(==, VisibleList, VisibleList)                                  }
      {(\, Command, VisibleList)                                       }
      {(\, Function, VisibleList)                                      }
      {(\, SelfInitializingType, VisibleList)                          }
      {(_, VisibleList, List)                                          }
      {(_, VisibleList, ZZ)                                            }
      {({*Function*}, VisibleList)                                     }
      {(accumulate, Function, Thing, VisibleList)                      }
      {(accumulate, Function, VisibleList)                             }
      {(accumulate, VisibleList, Function)                             }
      {(accumulate, VisibleList, Thing, Function)                      }
      {(between, Thing, VisibleList)                                   }
      {(briefDocumentation, VisibleList)                               }
      {(commonest, VisibleList)                                        }
      {(EXAMPLE, VisibleList)                                          }
      {(expression, VisibleList)                                       }
      {(flatten, VisibleList)                                          }
      {(fold, Function, Thing, VisibleList)                            }
      {(fold, Function, VisibleList)                                   }
      {(fold, VisibleList, Function)                                   }
      {(fold, VisibleList, Thing, Function)                            }
      {(insert, ZZ, Thing, VisibleList)                                }
      {(isSorted, VisibleList)                                         }
      {(isSubset, Set, VisibleList)                                    }
      {(isSubset, VisibleList, Set)                                    }
      {(isSubset, VisibleList, VisibleList)                            }
      {(length, VisibleList)                                           }
      {(max, VisibleList)                                              }
      {(member, Thing, VisibleList)                                    }
      {(min, VisibleList)                                              }
      {(netList, VisibleList)                                          }
      {(numeric, VisibleList)                                          }
      {(numeric, ZZ, VisibleList)                                      }
      {(part, InfiniteNumber, InfiniteNumber, VisibleList, RingElement)}
      {(part, InfiniteNumber, ZZ, VisibleList, RingElement)            }
      {(part, Nothing, Nothing, VisibleList, RingElement)              }
      {(part, Nothing, ZZ, VisibleList, RingElement)                   }
      {(part, ZZ, InfiniteNumber, VisibleList, RingElement)            }
      {(part, ZZ, Nothing, VisibleList, RingElement)                   }
      {(part, ZZ, VisibleList, RingElement)                            }
      {(part, ZZ, ZZ, VisibleList, RingElement)                        }
      {(partition, Function, VisibleList)                              }
      {(permutations, VisibleList)                                     }
      {(position, VisibleList, Function)                               }
      {(position, VisibleList, VisibleList, Function)                  }
      {(positions, VisibleList, Function)                              }
      {(product, VisibleList, Function)                                }
      {(product, VisibleList, VisibleList, Function)                   }
      {(replace, ZZ, Thing, VisibleList)                               }
      {(rle, VisibleList)                                              }
      {(rotate, ZZ, VisibleList)                                       }
      {(runLengthEncode, VisibleList)                                  }
      {(Schubert, ZZ, ZZ, VisibleList)                                 }
      {(set, VisibleList)                                              }
      {(sublists, VisibleList, Function)                               }
      {(sublists, VisibleList, Function, Function)                     }
      {(sublists, VisibleList, Function, Function, Function)           }
      {(sublists, VisibleList, Function, Function, Nothing)            }
      {(sublists, VisibleList, Function, Nothing)                      }
      {(sublists, VisibleList, Function, Nothing, Function)            }
      {(sublists, VisibleList, Function, Nothing, Nothing)             }
      {(submatrix', Matrix, Nothing, VisibleList)                      }
      {(submatrix', Matrix, VisibleList)                               }
      {(submatrix', Matrix, VisibleList, Nothing)                      }
      {(submatrix', Matrix, VisibleList, VisibleList)                  }
      {(submatrix, Matrix, Nothing, VisibleList)                       }
      {(submatrix, Matrix, VisibleList)                                }
      {(submatrix, Matrix, VisibleList, Nothing)                       }
      {(submatrix, Matrix, VisibleList, VisibleList)                   }
      {(sum, VisibleList, Function)                                    }
      {(sum, VisibleList, VisibleList, Function)                       }
      {(switch, ZZ, ZZ, VisibleList)                                   }
      {(t, VisibleList)                                                }
      {(tally, VisibleList)                                            }

o62 : VerticalList

i63 : methods List

o63 = {(*, Thing, List)                            }
      {(++, OptionTable, List)                     }
      {(+, List, List)                             }
      {(-, List)                                   }
      {(-, List, List)                             }
      {(-, List, Set)                              }
      {(-, Set, List)                              }
      {(.., List, List)                            }
      {(..<, List, List)                           }
      {(/, List, Command)                          }
      {(/, List, Function)                         }
      {(/, List, RingMap)                          }
      {(/, List, SelfInitializingType)             }
      {(/, List, Thing)                            }
      {(/, Module, List)                           }
      {(/, Ring, List)                             }
      {(<<, List, Thing)                           }
      {(>>, List, Function)                        }
      {(?, List, List)                             }
      {(\, RingMap, List)                          }
      {(^, Matrix, List)                           }
      {(^, Module, List)                           }
      {(^, Ring, List)                             }
      {(^, SheafOfRings, List)                     }
      {(_, Ideal, List)                            }
      {(_, Matrix, List)                           }
      {(_, Module, List)                           }
      {(_, Monoid, List)                           }
      {(_, PolynomialRing, List)                   }
      {(_, Ring, List)                             }
      {(_, VisibleList, List)                      }
      {({*Function*}, List)                        }
      {({*Function*}, List)                        }
      {({*Function*}, List)                        }
      {({*Function*}, List)                        }
      {({*Function*}, List, Function)              }
      {({*Function*}, Ring, List)                  }
      {(|, List, List)                             }
      {(ascii, List)                               }
      {(basis, InfiniteNumber, List, Ideal)        }
      {(basis, InfiniteNumber, List, Module)       }
      {(basis, InfiniteNumber, List, Ring)         }
      {(basis, List, Ideal)                        }
      {(basis, List, InfiniteNumber, Ideal)        }
      {(basis, List, InfiniteNumber, Module)       }
      {(basis, List, InfiniteNumber, Ring)         }
      {(basis, List, List, Ideal)                  }
      {(basis, List, List, Module)                 }
      {(basis, List, List, Ring)                   }
      {(basis, List, Module)                       }
      {(basis, List, Ring)                         }
      {(basis, List, ZZ, Ideal)                    }
      {(basis, List, ZZ, Ring)                     }
      {(basis, ZZ, List, Ideal)                    }
      {(basis, ZZ, List, Ring)                     }
      {(chainComplex, List)                        }
      {(code, List)                                }
      {(columnPermute, MutableMatrix, ZZ, List)    }
      {(commonRing, List)                          }
      {(degreesMonoid, List)                       }
      {(degreesRing, List)                         }
      {(diagonalMatrix, List)                      }
      {(diagonalMatrix, Ring, List)                }
      {(diagonalMatrix, Ring, ZZ, ZZ, List)        }
      {(diagonalMatrix, RingFamily, List)          }
      {(diagonalMatrix, RingFamily, ZZ, ZZ, List)  }
      {(diagonalMatrix, ZZ, ZZ, List)              }
      {(directSum, List)                           }
      {(document, List)                            }
      {(drop, BasicList, List)                     }
      {(dual, MonomialIdeal, List)                 }
      {(eliminate, Ideal, List)                    }
      {(eliminate, List, Ideal)                    }
      {(export, List)                              }
      {(exportMutable, List)                       }
      {(findFiles, List)                           }
      {(gcd, List)                                 }
      {(gcdLLL, List)                              }
      {(generateAssertions, List)                  }
      {(gradedModule, List)                        }
      {(gradedModuleMap, List)                     }
      {(hashTable, List)                           }
      {(help, List)                                }
      {(hilbertFunction, List, CoherentSheaf)      }
      {(hilbertFunction, List, Ideal)              }
      {(hilbertFunction, List, Module)             }
      {(hilbertFunction, List, ProjectiveVariety)  }
      {(hilbertFunction, List, Ring)               }
      {(homogenize, Matrix, RingElement, List)     }
      {(homogenize, Module, RingElement, List)     }
      {(homogenize, RingElement, RingElement, List)}
      {(homogenize, Vector, RingElement, List)     }
      {(hypertext, List)                           }
      {(ideal, List)                               }
      {(intersect, List)                           }
      {(lcm, List)                                 }
      {(listSymbols, List)                         }
      {(makePackageIndex, List)                    }
      {(map, Module, Module, List)                 }
      {(map, Module, Module, RingMap, List)        }
      {(map, Module, Nothing, List)                }
      {(map, Module, Nothing, RingMap, List)       }
      {(map, Module, ZZ, List)                     }
      {(map, Ring, Ring, List)                     }
      {(mathML, List)                              }
      {(matrix, List)                              }
      {(matrix, Ring, List)                        }
      {(matrix, RingFamily, List)                  }
      {(memoize, Function, List)                   }
      {(monoid, List)                              }
      {(monomialIdeal, List)                       }
      {(mutableMatrix, List)                       }
      {(net, List)                                 }
      {(NewFromMethod, DocumentTag, List)          }
      {(NewFromMethod, HashTable, List)            }
      {(NewFromMethod, Module, List)               }
      {(NewFromMethod, Set, List)                  }
      {(norm, List)                                }
      {(ofClass, List)                             }
      {(part, List, RingElement)                   }
      {(peek', ZZ, List)                           }
      {(plethysm, List, RingElement)               }
      {(precedence, List)                          }
      {(pretty2, List)                             }
      {(product, List)                             }
      {(promote, List, QQ, QQ)                     }
      {(promote, List, ZZ, QQ)                     }
      {(promote, List, ZZ, ZZ)                     }
      {(random, List)                              }
      {(random, List, Ring)                        }
      {(rowPermute, MutableMatrix, ZZ, List)       }
      {(rsort, List)                               }
      {(scanLines, Function, List)                 }
      {(searchPath, List, String)                  }
      {(selectVariables, List, PolynomialRing)     }
      {(sort, List)                                }
      {(SPACE, HeaderType, List)                   }
      {(SPACE, Ring, List)                         }
      {(SPACE, WrapperType, List)                  }
      {(standardPairs, MonomialIdeal, List)        }
      {(subsets, List)                             }
      {(subsets, List, ZZ)                         }
      {(substitute, Ideal, List)                   }
      {(substitute, Matrix, List)                  }
      {(substitute, Module, List)                  }
      {(substitute, RingElement, List)             }
      {(substitute, Vector, List)                  }
      {(sum, List)                                 }
      {(SYNOPSIS, List)                            }
      {(take, BasicList, List)                     }
      {(TEST, List)                                }
      {(texMath, List)                             }
      {(transpose, List)                           }
      {(truncate, List, Ideal)                     }
      {(truncate, List, Module)                    }
      {(undocumented, List)                        }
      {(unique, List)                              }
      {(vars, List)                                }
      {(weightRange, List, RingElement)            }

o63 : VerticalList

i64 : Partition {3,4,5}
stdio:65:1:(3): error: no method for adjacent objects:
--            Partition (of class Type)
--    SPACE   {3, 4, 5} (of class List)

i65 : new Partition from {3,4,5}

o65 = Partition{3, 4, 5}

o65 : Partition

i66 : new List from Matrix := (List,m) -> entries m				    -- proposed by Charley Crissman

o66 = {*Function[stdio:67:33-67:44]*}

o66 : FunctionClosure

i67 : R = QQ[x..z];

i68 : new List from vars R

o68 = {{x, y, z}}

o68 : List

i70 : new HashTable from { a => 1 }

o70 = HashTable{a => 1}

o70 : HashTable

i71 : HashTable from { a => 1 }
stdio:72:11:(3): error: syntax error at 'from'

i71 : new Matrix from { a => 1 }

--error or time limit reached in conversion of output to net: type 'debugError()' to run it again; will try conversion to string

--error in conversion of output to string
stdio:72:15:(3): error: at print: --backtrace update-- 

o71 : Matrixstdio:72:15:(3): error: after print: --backtrace update-- 

i72 : make

o72 = make

o72 : Symbol

i73 : make Matrix from { 1 }
stdio:74:13:(3): error: syntax error at 'from'

i73 : make Matrix from {{ 1 }}
stdio:74:29:(3): error: syntax error at 'from'

i73 : for i from (1,1,1,1,1,1) to (1,2,3,4,5,6) do print i
stdio:74:54:(3): error: expected an integer

i74 : for i from 4 to 0 by -1 do nothing
stdio:75:17:(3): error: no method for adjacent objects:
--            0 (of class ZZ)
--    SPACE   by (of class Symbol)

i75 : for i to 0 from 4 do nothing
stdio:76:12:(3): error: syntax error : expected 'do' or 'list'
stdio:76:1:(3): error:  ... to match this 'for'

i75 : for i from (1,1,1,1,1,1) to (1,2,3,4,5,6) by (-1,-1,-1,-1,-1,-1) do print i
stdio:76:37:(3): error: expected an integer

i76 : QQ[x]

o76 = QQ[x]

o76 : PolynomialRing

i77 : for i from x to x+10 do print
stdio:78:12:(3): error: expected an integer

i78 : QQ[x,y]

o78 = QQ[x, y]

o78 : PolynomialRing

i79 : for i from x to x+10*y by y do print
stdio:80:12:(3): error: expected an integer

i81 : for i from 0 to 10 when i < 5 do print i
0
1
2
3
4

i82 : R = QQ[x,y]

o82 = R

o82 : PolynomialRing

i83 : M = coker matrix "x,0,0;0,y,0"

o83 = cokernel | x 0 0 |
               | 0 y 0 |

                             2
o83 : R-module, quotient of R

i84 : M_{0,1}

o84 = | 1 0 |
      | 0 1 |

o84 : Matrix

i85 : target oo

o85 = cokernel | x 0 0 |
               | 0 y 0 |

                             2
o85 : R-module, quotient of R

i86 : source ooo

       2
o86 = R

o86 : R-module, free

i87 : image o84

o87 = subquotient (| 1 0 |, | x 0 0 |)
                   | 0 1 |  | 0 y 0 |

                                2
o87 : R-module, subquotient of R

i89 : prune o87

o89 = cokernel | x 0 |
               | 0 y |

                             2
o89 : R-module, quotient of R

i90 : M_1

o90 = | 0 |
      | 1 |

o90 : cokernel | x 0 0 |
               | 0 y 0 |

i91 : R * M_1

o91 = subquotient (| 0 |, | x 0 0 |)
                   | 1 |  | 0 y 0 |

                                2
o91 : R-module, subquotient of R

i92 : R * M_1 + R*M_0

o92 = subquotient (| 0 1 |, | x 0 0 |)
                   | 1 0 |  | 0 y 0 |

                                2
o92 : R-module, subquotient of R

i93 : I = ideal x

o93 = ideal(x)

o93 : Ideal of R

i94 : I * M_1 + R*M_0

o94 = subquotient (| 0 1 |, | x 0 0 |)
                   | x 0 |  | 0 y 0 |

                                2
o94 : R-module, subquotient of R

i95 : viewHelp 

i96 : 

Process M2 finished

