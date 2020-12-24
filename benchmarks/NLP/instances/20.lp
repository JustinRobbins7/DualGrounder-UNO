% instance 20
goal(c(inst,geton20,getting_on)).
goal(c(agent_get_on,geton20,bill20)).
goal(c(name,bill20,bill)).
goal(c(patient_get_on,geton20,bus20)).
goal(c(inst,bus20,bus)).
goal(c(precede,geton20,getoff20)).
goal(c(inst,getoff20,getting_off)).
goal(c(agent_get_off,getoff20,bill20)).
goal(c(place_get_off,getoff20,rest20)).
goal(c(inst,rest20,restaurant)).
goal(c(precede,getoff20,drink20)).
goal(c(inst,drink20,drinking)).
goal(c(drinker,drink20,bill20)).
goal(c(patient_drink,drink20,ms20)).
goal(c(inst,ms20,milkshake)).
goal(c(instr_drink,drink20,str20)).
goal(c(inst,str20,straw)).
