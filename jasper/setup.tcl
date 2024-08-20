analyze -sv ../picorv32/picorv32.v +define+FORMAL                                                                                          
elaborate -top picorv32                                                                                                        
clock clk                                                                                                                      
reset ~resetn                                                                                                                  
