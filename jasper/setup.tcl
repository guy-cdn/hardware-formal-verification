analyze -sv ../picorv32/picorv32.v +define+RISCV_FORMAL                                                                                          
elaborate -top picorv32                                                                                                        
clock clk                                                                                                                      
reset ~resetn                                                                                                                  
