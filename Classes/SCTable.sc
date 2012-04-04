// pcslib-sc 2011
// Set Class Table

SCTable {
	classvar <table;
	classvar indexFromName, indexFromPF;
	
	*indexOf { arg x;
		var ret;
		if(x.class == PCS, {
			if(indexFromPF.includesKey(x.pf.pcsHash), {
				^indexFromPF.at(x.pf.pcsHash);
			}, {
				///*
				"forma erronea".postln;
				x.pf.postln;
				^nil;
				//*/
				/*
				"forma erronea intentando inversion (workaround for crash)".postln;
				^indexFromPF.at(x.i.pf.pcsHash);
				*/
			});
		}, {
			ret = indexFromName.at(x.asSymbol);
			ret ?? {
				ret = 0;
				("PCS" + x + "doesn't exist, returning empty PCS").warn;
			};
			^ret;
		});
	}
	
	*entryOf { arg x;
		^table.at(SCTable.indexOf(x));
	}
	
	*nameOf { arg pcs;
		if(SCTable.indexOf(pcs).notNil, {
			^table.at(SCTable.indexOf(pcs)).at(0);
		}, { ^nil });
	}
	
	*pfOf { arg name;
		^table.at(SCTable.indexOf(name)).at(1);
	}
	
	*initClass {
		var time;
		time = bench {
		// ver valores del conjunto nulo (y checkear problemas).
		// 0 = name, 1 = pf, 2 = mmi, 3 = Z, 4 = icv, 5 = iv, 6 = cint1
		table = [
			[ '0-0', PCS[], 0, nil, [0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [] ],
			[ '1-1', PCS[0], 1, nil, [1, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 11, 11, 11, 11], [0] ],

			[ '2-1', PCS[0, 1], 5, nil, [2, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 9, 9, 8, 8], [1, 11] ],
			[ '2-2', PCS[0, 2], 2, nil, [2, 0, 1, 0, 0, 0, 0], [1, 1, 1, 1, 9, 9, 9, 9], [2, 10] ],
			[ '2-3', PCS[0, 3], 3, nil, [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 1, 9, 9, 9, 9], [3, 9] ],
			[ '2-4', PCS[0, 4], 4, nil, [2, 0, 0, 0, 1, 0, 0], [1, 1, 1, 1, 9, 9, 9, 9], [4, 8] ],
			[ '2-5', PCS[0, 5], 1, nil, [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 9, 9, 8, 8], [5, 7] ],
			[ '2-6', PCS[0, 6], 6, nil, [2, 0, 0, 0, 0, 0, 1], [2, 2, 2, 2, 10, 10, 10, 10], [6, 6] ],

			[ '3-1', PCS[0, 1, 2], 9, nil, [3, 2, 1, 0, 0, 0, 0], [1, 1, 0, 0, 7, 7, 4, 4], [1, 1, 10] ],
			[ '3-2', PCS[0, 1, 3], 7, nil, [3, 1, 1, 1, 0, 0, 0], [1, 0, 0, 0, 5, 6, 5, 5], [1, 2, 9] ],
			[ '3-3', PCS[0, 1, 4], 11, nil, [3, 1, 0, 1, 1, 0, 0], [1, 0, 0, 0, 5, 6, 5, 5], [1, 3, 8] ],
			[ '3-4', PCS[0, 1, 5], 4, nil, [3, 1, 0, 0, 1, 1, 0], [1, 0, 1, 0, 5, 6, 5, 6], [1, 4, 7] ],
			[ '3-5', PCS[0, 1, 6], 5, nil, [3, 1, 0, 0, 0, 1, 1], [1, 0, 0, 1, 6, 7, 7, 6], [1, 5, 6] ],
			[ '3-6', PCS[0, 2, 4], 6, nil, [3, 0, 2, 0, 1, 0, 0], [1, 1, 1, 1, 7, 7, 7, 7], [2, 2, 8] ],
			[ '3-7', PCS[0, 2, 5], 2, nil, [3, 0, 1, 1, 0, 1, 0], [1, 0, 0, 0, 5, 6, 5, 5], [2, 3, 7] ],
			[ '3-8', PCS[0, 2, 6], 8, nil, [3, 0, 1, 0, 1, 0, 1], [1, 0, 0, 1, 6, 7, 7, 6], [2, 4, 6] ],
			[ '3-9', PCS[0, 2, 7], 1, nil, [3, 0, 1, 0, 0, 2, 0], [1, 1, 0, 0, 7, 7, 4, 4], [2, 5, 5] ],
			[ '3-10', PCS[0, 3, 6], 10, nil, [3, 0, 0, 2, 0, 0, 1], [1, 1, 1, 1, 8, 8, 8, 8], [3, 3, 6] ],
			[ '3-11', PCS[0, 3, 7], 3, nil, [3, 0, 0, 1, 1, 1, 0], [1, 0, 0, 0, 5, 6, 5, 5], [3, 4, 5] ],
			[ '3-12', PCS[0, 4, 8], 12, nil, [3, 0, 0, 0, 3, 0, 0], [3, 3, 3, 3, 9, 9, 9, 9], [4, 4, 4] ],

			[ '4-1', PCS[0, 1, 2, 3], 23, nil, [4, 3, 2, 1, 0, 0, 0], [1, 1, 0, 0, 5, 5, 1, 1], [1, 1, 1, 9] ],
			[ '4-2', PCS[0, 1, 2, 4], 22, nil, [4, 2, 2, 1, 1, 0, 0], [1, 0, 0, 0, 3, 4, 1, 1], [1, 1, 2, 8] ],
			[ '4-3', PCS[0, 1, 3, 4], 26, nil, [4, 2, 1, 2, 1, 0, 0], [1, 1, 0, 0, 3, 3, 2, 2], [1, 2, 1, 8] ],
			[ '4-4', PCS[0, 1, 2, 5], 14, nil, [4, 2, 1, 1, 1, 1, 0], [1, 0, 0, 0, 1, 3, 2, 3], [1, 1, 3, 7] ],
			[ '4-5', PCS[0, 1, 2, 6], 16, nil, [4, 2, 1, 0, 1, 1, 1], [1, 0, 0, 0, 2, 4, 3, 2], [1, 1, 4, 6] ],
			[ '4-6', PCS[0, 1, 2, 7], 6, nil, [4, 2, 1, 0, 0, 2, 1], [1, 1, 1, 1, 4, 4, 4, 4], [1, 1, 5, 5] ],
			[ '4-7', PCS[0, 1, 4, 5], 20, nil, [4, 2, 0, 1, 2, 1, 0], [1, 1, 0, 0, 3, 3, 3, 3], [1, 3, 1, 7] ],
			[ '4-8', PCS[0, 1, 5, 6], 8, nil, [4, 2, 0, 0, 1, 2, 1], [1, 1, 1, 1, 4, 4, 4, 4], [1, 4, 1, 6] ],
			[ '4-9', PCS[0, 1, 6, 7], 9, nil, [4, 2, 0, 0, 0, 2, 2], [2, 2, 2, 2, 6, 6, 6, 6], [1, 5, 1, 5] ],
			[ '4-10', PCS[0, 2, 3, 5], 10, nil, [4, 1, 2, 2, 0, 1, 0], [1, 1, 1, 1, 3, 3, 3, 3], [2, 1, 2, 7] ],
			[ '4-11', PCS[0, 1, 3, 5], 11, nil, [4, 1, 2, 1, 1, 1, 0], [1, 0, 1, 0, 1, 3, 1, 3], [1, 2, 2, 7] ],
			[ '4-12', PCS[0, 2, 3, 6], 27, nil, [4, 1, 1, 2, 1, 0, 1], [1, 0, 0, 0, 2, 4, 3, 2], [2, 1, 3, 6] ],
			[ '4-13', PCS[0, 1, 3, 6], 13, nil, [4, 1, 1, 2, 0, 1, 1], [1, 0, 0, 1, 2, 4, 4, 2], [1, 2, 3, 6] ],
			[ '4-14', PCS[0, 2, 3, 7], 4, nil, [4, 1, 1, 1, 1, 2, 0], [1, 0, 0, 0, 1, 3, 2, 3], [2, 1, 4, 5] ],
			[ '4-15', PCS[0, 1, 4, 6], 29, '29', [4, 1, 1, 1, 1, 1, 1], [1, 0, 0, 0, 0, 3, 3, 1], [1, 3, 2, 6] ],
			[ '4-16', PCS[0, 1, 5, 7], 5, nil, [4, 1, 1, 0, 1, 2, 1], [1, 0, 0, 0, 2, 4, 3, 2], [1, 4, 2, 5] ],
			[ '4-17', PCS[0, 3, 4, 7], 17, nil, [4, 1, 0, 2, 2, 1, 0], [1, 1, 1, 1, 3, 3, 3, 3], [3, 1, 3, 5] ],
			[ '4-18', PCS[0, 1, 4, 7], 18, nil, [4, 1, 0, 2, 1, 1, 1], [1, 0, 0, 1, 2, 4, 4, 2], [1, 3, 3, 5] ],
			[ '4-19', PCS[0, 1, 4, 8], 19, nil, [4, 1, 0, 1, 3, 1, 0], [1, 0, 1, 0, 3, 5, 3, 5], [1, 3, 4, 4] ],
			[ '4-20', PCS[0, 1, 5, 8], 7, nil, [4, 1, 0, 1, 2, 2, 0], [1, 1, 0, 0, 3, 3, 3, 3], [1, 4, 3, 4] ],
			[ '4-21', PCS[0, 2, 4, 6], 21, nil, [4, 0, 3, 0, 2, 0, 1], [1, 1, 1, 1, 6, 6, 6, 6], [2, 2, 2, 6] ],
			[ '4-22', PCS[0, 2, 4, 7], 2, nil, [4, 0, 2, 1, 1, 2, 0], [1, 0, 0, 0, 3, 4, 1, 1], [2, 2, 3, 5] ],
			[ '4-23', PCS[0, 2, 5, 7], 1, nil, [4, 0, 2, 0, 3, 0, 1], [1, 1, 1, 1, 6, 6, 6, 6], [2, 2, 4, 4] ],
			[ '4-24', PCS[0, 2, 4, 8], 24, nil, [5, 0, 2, 0, 3, 0, 1], [1, 1, 1, 1, 6, 6, 6, 6], [2, 2, 4, 4] ],
			[ '4-25', PCS[0, 2, 6, 8], 25, nil, [4, 0, 2, 0, 2, 0, 2], [2, 2, 2, 2, 6, 6, 6, 6], [2, 4, 2, 4] ],
			[ '4-26', PCS[0, 3, 5, 8], 3, nil, [4, 0, 1, 2, 1, 2, 0], [1, 1, 0, 0, 3, 3, 2, 2], [3, 2, 3, 4] ],
			[ '4-27', PCS[0, 2, 5, 8], 12, nil, [4, 0, 1, 2, 1, 1, 1], [1, 0, 0, 0, 2, 4, 3, 2], [2, 3, 3, 4] ],
			[ '4-28', PCS[0, 3, 6, 9], 28, nil, [4, 0, 0, 4, 0, 0, 2], [4, 4, 4, 4, 8, 8, 8, 8], [3, 3, 3, 3] ],
			[ '4-29', PCS[0, 1, 3, 7], 15, '15', [4, 1, 1, 1, 1, 1, 1], [1, 0, 0, 0, 0, 3, 3, 1], [1, 2, 4, 5] ],

			[ '5-1', PCS[0, 1, 2, 3, 4], 35, nil, [5, 4, 3, 2, 1, 0, 0], [1, 1, 0, 0, 3, 3, 0, 0], [1, 1, 1, 1, 8] ],
			[ '5-2', PCS[0, 1, 2, 3, 5], 23, nil, [5, 3, 3, 2, 1, 1, 0], [1, 0, 0, 0, 1, 2, 1, 1], [1, 1, 1, 2, 7] ],
			[ '5-3', PCS[0, 1, 2, 4, 5], 27, nil, [5, 3, 2, 2, 2, 1, 0], [1, 0, 0, 0, 1, 1, 1, 0], [1, 1, 2, 1, 7] ],
			[ '5-4', PCS[0, 1, 2, 3, 6], 29, nil, [5, 3, 2, 2, 1, 1, 1], [1, 0, 0, 0, 0, 2, 0, 0], [1, 1, 1, 3, 6] ],
			[ '5-5', PCS[0, 1, 2, 3, 7], 14, nil, [5, 3, 2, 1, 1, 2, 1], [1, 0, 0, 0, 0, 1, 1, 1], [1, 1, 1, 4, 5] ],
			[ '5-6', PCS[0, 1, 2, 5, 6], 20, nil, [5, 3, 1, 1, 2, 2, 1], [1, 0, 0, 0, 0, 1, 1, 1], [1, 1, 3, 1, 6] ],
			[ '5-7', PCS[0, 1, 2, 6, 7], 7, nil, [5, 3, 1, 0, 1, 3, 2], [1, 0, 0, 1, 2, 3, 3, 2], [1, 1, 4, 1, 5] ],
			[ '5-8', PCS[0, 2, 3, 4, 6], 34, nil, [5, 2, 3, 2, 2, 0, 1], [1, 1, 0, 0, 2, 2, 0, 0], [2, 1, 1, 2, 6] ],
			[ '5-9', PCS[0, 1, 2, 4, 6], 24, nil, [5, 2, 3, 1, 2, 1, 1], [1, 0, 0, 0, 0, 2, 0, 1], [1, 1, 2, 2, 6] ],
			[ '5-10', PCS[0, 1, 3, 4, 6], 25, nil, [5, 2, 2, 3, 1, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0], [1, 2, 1, 2, 6] ],
			[ '5-11', PCS[0, 2, 3, 4, 7], 11, nil, [5, 2, 2, 2, 2, 2, 0], [1, 0, 1, 0, 1, 1, 1, 1], [2, 1, 1, 3, 5] ],
			[ '5-12', PCS[0, 1, 3, 5, 6], 12, '36', [5, 2, 2, 2, 1, 2, 1], [1, 1, 1, 1, 0, 0, 0, 0], [1, 2, 2, 1, 6] ],
			[ '5-13', PCS[0, 1, 2, 4, 8], 30, nil, [5, 2, 2, 1, 3, 1, 1], [1, 0, 0, 0, 0, 2, 0, 1], [1, 1, 2, 4, 4] ],
			[ '5-14', PCS[0, 1, 2, 5, 7], 5, nil, [5, 2, 2, 1, 1, 3, 1], [1, 0, 0, 0, 0, 1, 1, 1], [1, 1, 3, 2, 5] ],
			[ '5-15', PCS[0, 1, 2, 6, 8], 15, nil, [5, 2, 2, 0, 2, 2, 2], [1, 1, 1, 1, 2, 2, 2, 2], [1, 1, 4, 2, 4] ],
			[ '5-16', PCS[0, 1, 3, 4, 7], 32, nil, [5, 2, 1, 3, 2, 1, 1], [1, 0, 0, 0, 0, 1, 1, 0], [1, 2, 1, 3, 5] ],
			[ '5-17', PCS[0, 1, 3, 4, 8], 37, '37', [5, 2, 1, 2, 3, 2, 0], [1, 1, 0, 0, 1, 1, 2, 2], [1, 2, 1, 4, 4] ],
			[ '5-18', PCS[0, 1, 4, 5, 7], 38, '38', [5, 2, 1, 2, 2, 2, 1], [1, 0, 0, 0, 0, 1, 1, 0], [1, 3, 1, 2, 5] ],
			[ '5-19', PCS[0, 1, 3, 6, 7], 19, nil, [5, 2, 1, 2, 1, 2, 2], [1, 0, 0, 1, 0, 2, 2, 0], [1, 2, 3, 1, 5] ],
			[ '5-20', PCS[0, 1, 3, 7, 8], 6, nil, [5, 2, 1, 1, 2, 3, 1], [1, 0, 0, 0, 0, 1, 1, 1], [1, 2, 4, 1, 4] ],
			[ '5-21', PCS[0, 1, 4, 5, 8], 21, nil, [5, 2, 0, 2, 4, 2, 0], [1, 0, 1, 0, 3, 3, 3, 3], [1, 3, 1, 3, 4] ],
			[ '5-22', PCS[0, 1, 4, 7, 8], 22, nil, [5, 2, 0, 2, 3, 2, 1], [1, 1, 1, 1, 2, 2, 2, 2], [1, 3, 3, 1, 4] ],
			[ '5-23', PCS[0, 2, 3, 5, 7], 2, nil, [5, 1, 3, 2, 1, 3, 0], [1, 0, 0, 0, 1, 2, 1, 1], [2, 1, 2, 2, 5] ],
			[ '5-24', PCS[0, 1, 3, 5, 7], 9, nil, [5, 1, 3, 1, 2, 2, 1], [1, 0, 0, 0, 0, 2, 0, 1], [1, 2, 2, 2, 5] ],
			[ '5-25', PCS[0, 2, 3, 5, 8], 10, nil, [5, 1, 2, 3, 1, 2, 1], [1, 0, 0, 0, 0, 1, 1, 0], [2, 1, 2, 3, 4] ],
			[ '5-26', PCS[0, 2, 4, 5, 8], 26, nil, [5, 1, 2, 2, 3, 1, 1], [1, 0, 1, 0, 0, 2, 0, 2], [2, 2, 1, 3, 4] ],
			[ '5-27', PCS[0, 1, 3, 5, 8], 3, nil, [5, 1, 2, 2, 2, 3, 0], [1, 0, 0, 0, 1, 1, 1, 0], [1, 2, 2, 3, 4] ],
			[ '5-28', PCS[0, 2, 3, 6, 8], 28, nil, [5, 1, 2, 2, 2, 1, 2], [1, 0, 0, 1, 0, 2, 2, 0], [2, 1, 3, 2, 4] ],
			[ '5-29', PCS[0, 1, 3, 6, 8], 4, nil, [5, 1, 2, 2, 1, 3, 1], [1, 0, 0, 0, 0, 2, 0, 0], [1, 2, 3, 2, 4] ],
			[ '5-30', PCS[0, 1, 4, 6, 8], 13, nil, [5, 1, 2, 1, 3, 2, 1], [1, 0, 0, 0, 0, 2, 0, 1], [1, 3, 2, 2, 4] ],
			[ '5-31', PCS[0, 1, 3, 6, 9], 31, nil, [5, 1, 1, 4, 1, 1, 2], [1, 0, 0, 1, 0, 3, 3, 0], [1, 2, 3, 3, 3] ],
			[ '5-32', PCS[0, 1, 4, 6, 9], 16, nil, [5, 1, 1, 3, 2, 2, 1], [1, 0, 0, 0, 0, 1, 1, 0], [1, 3, 2, 3, 3] ],
			[ '5-33', PCS[0, 2, 4, 6, 8], 33, nil, [5, 0, 4, 0, 4, 0, 2], [1, 1, 1, 1, 6, 6, 6, 6], [2, 2, 2, 2, 4] ],
			[ '5-34', PCS[0, 2, 4, 6, 9], 8, nil, [5, 0, 3, 2, 2, 2, 1], [1, 1, 0, 0, 2, 2, 0, 0], [2, 2, 2, 3, 3] ],
			[ '5-35', PCS[0, 2, 4, 7, 9], 1, nil, [5, 0, 3, 2, 1, 4, 0], [1, 1, 0, 0, 3, 3, 0, 0], [2, 2, 3, 2, 3] ],
			[ '5-36', PCS[0, 1, 2, 4, 7], 36, '12', [5, 2, 2, 2, 1, 2, 1], [1, 0, 0, 1, 0, 1, 1, 0], [1, 1, 2, 3, 5] ],
			[ '5-37', PCS[0, 3, 4, 5, 8], 17, '17', [5, 2, 1, 2, 3, 2, 0], [1, 1, 0, 0, 1, 1, 2, 2], [3, 1, 1, 3, 4] ],
			[ '5-38', PCS[0, 1, 2, 5, 8], 18, '18', [5, 2, 1, 2, 2, 2, 1], [1, 0, 0, 0, 0, 1, 1, 0], [1, 1, 3, 3, 4] ],

			[ '6-1', PCS[0, 1, 2, 3, 4, 5], 32, nil, [6, 5, 4, 3, 2, 1, 0], [1, 1, 0, 0, 1, 1, 0, 0], [1, 1, 1, 1, 1, 7] ],
			[ '6-2', PCS[0, 1, 2, 3, 4, 6], 33, nil, [6, 4, 4, 3, 2, 1, 1], [1, 0, 0, 0, 0, 1, 0, 0], [1, 1, 1, 1, 2, 6] ],
			[ '6-3', PCS[0, 1, 2, 3, 5, 6], 25, '36', [6, 4, 3, 3, 2, 2, 1], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 2, 1, 6] ],
			[ '6-4', PCS[0, 1, 2, 4, 5, 6], 26, '37', [6, 4, 3, 2, 3, 2, 1], [1, 1, 0, 0, 0, 0, 0, 0], [1, 1, 2, 1, 1, 6] ],
			[ '6-5', PCS[0, 1, 2, 3, 6, 7], 18, nil, [6, 4, 2, 2, 2, 3, 2], [1, 0, 0, 0, 0, 1, 0, 0], [1, 1, 1, 3, 1, 5] ],
			[ '6-6', PCS[0, 1, 2, 5, 6, 7], 38, '38', [6, 4, 2, 1, 2, 4, 2], [1, 1, 0, 0, 0, 0, 1, 1], [1, 1, 3, 1, 1, 5] ],
			[ '6-7', PCS[0, 1, 2, 6, 7, 8], 7, nil, [6, 4, 2, 0, 2, 4, 3], [2, 2, 2, 2, 2, 2, 2, 2], [1, 1, 4, 1, 1, 4] ],
			[ '6-8', PCS[0, 2, 3, 4, 5, 7], 8, nil, [6, 3, 4, 3, 2, 3, 0], [1, 1, 1, 1, 1, 1, 1, 1], [2, 1, 1, 1, 2, 5] ],
			[ '6-9', PCS[0, 1, 2, 3, 5, 7], 9, nil, [6, 3, 4, 2, 2, 3, 1], [1, 0, 1, 0, 0, 1, 0, 1], [1, 1, 1, 2, 2, 5] ],
			[ '6-10', PCS[0, 1, 3, 4, 5, 7], 46, '39', [6, 3, 3, 3, 3, 2, 1], [1, 0, 0, 0, 0, 0, 0, 0], [1, 2, 1, 1, 2, 5] ],
			[ '6-11', PCS[0, 1, 2, 4, 5, 7], 40, '40', [6, 3, 3, 3, 2, 3, 1], [1, 0, 0, 0, 0, 0, 1, 0], [1, 1, 2, 1, 2, 5] ],
			[ '6-12', PCS[0, 1, 2, 4, 6, 7], 12, '41', [6, 3, 3, 2, 2, 3, 2], [1, 0, 0, 1, 0, 0, 0, 0], [1, 1, 2, 2, 1, 5] ],
			[ '6-13', PCS[0, 1, 3, 4, 6, 7], 50, '42', [6, 3, 2, 4, 2, 2, 2], [1, 1, 0, 0, 0, 0, 0, 0], [1, 2, 1, 2, 1, 5] ],
			[ '6-14', PCS[0, 1, 3, 4, 5, 8], 14, nil, [6, 3, 2, 3, 4, 3, 0], [1, 0, 1, 0, 1, 0, 1, 0], [1, 2, 1, 1, 3, 4] ],
			[ '6-15', PCS[0, 1, 2, 4, 5, 8], 31, nil, [6, 3, 2, 3, 4, 2, 1], [1, 0, 0, 0, 0, 1, 0, 0], [1, 1, 2, 1, 3, 4] ],
			[ '6-16', PCS[0, 1, 4, 5, 6, 8], 16, nil, [6, 3, 2, 2, 4, 3, 1], [1, 0, 1, 0, 0, 1, 0, 1], [1, 3, 1, 1, 2, 4] ],
			[ '6-17', PCS[0, 1, 2, 4, 7, 8], 17, '43', [6, 3, 2, 2, 3, 3, 2], [1, 0, 0, 1, 0, 0, 0, 0], [1, 1, 2, 3, 1, 4] ],
			[ '6-18', PCS[0, 1, 2, 5, 7, 8], 5, nil, [6, 3, 2, 2, 2, 4, 2], [1, 0, 0, 0, 0, 1, 0, 0], [1, 1, 3, 2, 1, 4] ],
			[ '6-19', PCS[0, 1, 3, 4, 7, 8], 44, '44', [6, 3, 1, 3, 4, 3, 1], [1, 0, 0, 0, 0, 0, 1, 0], [1, 2, 1, 3, 1, 4] ],
			[ '6-20', PCS[0, 1, 4, 5, 8, 9], 20, nil, [6, 3, 0, 3, 6, 3, 0], [3, 3, 3, 3, 3, 3, 3, 3], [1, 3, 1, 3, 1, 3] ],
			[ '6-21', PCS[0, 2, 3, 4, 6, 8], 34, nil, [6, 2, 4, 2, 4, 1, 2], [1, 0, 0, 0, 0, 1, 0, 0], [2, 1, 1, 2, 2, 4] ],
			[ '6-22', PCS[0, 1, 2, 4, 6, 8], 22, nil, [6, 2, 4, 1, 4, 2, 2], [1, 0, 1, 0, 0, 1, 0, 1], [1, 1, 2, 2, 2, 4] ],
			[ '6-23', PCS[0, 2, 3, 5, 6, 8], 23, '45', [6, 2, 3, 4, 2, 2, 2], [1, 1, 1, 1, 0, 0, 0, 0], [2, 1, 2, 1, 2, 4] ],
			[ '6-24', PCS[0, 1, 3, 4, 6, 8], 39, '46', [6, 2, 3, 3, 3, 3, 1], [1, 0, 0, 0, 0, 0, 0, 0], [1, 2, 1, 2, 2, 4] ],
			[ '6-25', PCS[0, 1, 3, 5, 6, 8], 3, '47', [6, 2, 3, 3, 2, 4, 1], [1, 0, 0, 0, 0, 0, 0, 0], [1, 2, 2, 1, 2, 4] ],
			[ '6-26', PCS[0, 1, 3, 5, 7, 8], 4, '48', [6, 2, 3, 2, 3, 4, 1], [1, 1, 0, 0, 0, 0, 0, 0], [1, 2, 2, 2, 1, 4] ],
			[ '6-27', PCS[0, 1, 3, 4, 6, 9], 27, nil, [6, 2, 2, 5, 2, 2, 2], [1, 0, 0, 1, 0, 1, 1, 0], [1, 2, 1, 2, 3, 3] ],
			[ '6-28', PCS[0, 1, 3, 5, 6, 9], 28, '49', [6, 2, 2, 4, 3, 2, 2], [1, 1, 1, 1, 0, 0, 0, 0], [1, 2, 2, 1, 3, 3] ],
			[ '6-29', PCS[0, 1, 3, 6, 8, 9], 42, '50', [6, 2, 2, 4, 2, 3, 2], [1, 1, 0, 0, 0, 0, 0, 0], [1, 2, 3, 2, 1, 3] ],
			[ '6-30', PCS[0, 1, 3, 6, 7, 9], 30, nil, [6, 2, 2, 4, 2, 2, 3], [2, 0, 0, 2, 0, 2, 2, 0], [1, 2, 3, 1, 2, 3] ],
			[ '6-31', PCS[0, 1, 3, 5, 8, 9], 15, nil, [6, 2, 2, 3, 4, 3, 1], [1, 0, 0, 0, 0, 1, 0, 0], [1, 2, 2, 3, 1, 3] ],
			[ '6-32', PCS[0, 2, 4, 5, 7, 9], 1, nil, [6, 1, 4, 3, 2, 5, 0], [1, 1, 0, 0, 1, 1, 0, 0], [2, 2, 1, 2, 2, 3] ],
			[ '6-33', PCS[0, 2, 3, 5, 7, 9], 2, nil, [6, 1, 4, 3, 2, 4, 1], [1, 0, 0, 0, 0, 1, 0, 0], [2, 1, 2, 2, 2, 3] ],
			[ '6-34', PCS[0, 1, 3, 5, 7, 9], 21, nil, [6, 1, 4, 2, 4, 2, 2], [1, 0, 0, 0, 0, 1, 0, 0], [1, 2, 2, 2, 2, 3] ],
			[ '6-35', PCS[0, 2, 4, 6, 8, 10], 35, nil, [6, 0, 6, 0, 6, 0, 3], [6, 6, 6, 6, 6, 6, 6, 6], [2, 2, 2, 2, 2, 2] ],
			[ '6-36', PCS[0, 1, 2, 3, 4, 7], 47, '3', [6, 4, 3, 3, 2, 2, 1], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 3, 5] ],
			[ '6-37', PCS[0, 1, 2, 3, 4, 8], 48, '4', [6, 4, 3, 2, 3, 2, 1], [1, 1, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 4, 4] ],
			[ '6-38', PCS[0, 1, 2, 3, 7, 8], 6, '6', [6, 4, 2, 1, 2, 4, 2], [1, 1, 0, 0, 0, 0, 1, 1], [1, 1, 1, 4, 1, 4] ],
			[ '6-39', PCS[0, 2, 3, 4, 5, 8], 24, '10', [6, 3, 3, 3, 3, 2, 1], [1, 0, 0, 0, 0, 0, 0, 0], [2, 1, 1, 1, 3, 4] ],
			[ '6-40', PCS[0, 1, 2, 3, 5, 8], 11, '11', [6, 3, 3, 3, 2, 3, 1], [1, 0, 0, 0, 0, 0, 1, 0], [1, 1, 1, 2, 3, 4] ],
			[ '6-41', PCS[0, 1, 2, 3, 6, 8], 41, '12', [6, 3, 3, 2, 2, 3, 2], [1, 0, 0, 1, 0, 0, 0, 0], [1, 1, 1, 3, 2, 4] ],
			[ '6-42', PCS[0, 1, 2, 3, 6, 9], 29, '13', [6, 3, 2, 4, 2, 2, 2], [1, 1, 0, 0, 0, 0, 0, 0], [1, 1, 1, 3, 3, 3] ],
			[ '6-43', PCS[0, 1, 2, 5, 6, 8], 43, '17', [6, 3, 2, 2, 3, 3, 2], [1, 0, 0, 1, 0, 0, 0, 0], [1, 1, 3, 1, 2, 4] ],
			[ '6-44', PCS[0, 1, 2, 5, 6, 9], 19, '19', [6, 3, 1, 3, 4, 3, 1], [1, 0, 0, 0, 0, 0, 1, 0], [1, 1, 3, 1, 3, 3] ],
			[ '6-45', PCS[0, 2, 3, 4, 6, 9], 45, '23', [6, 2, 3, 4, 2, 2, 2], [1, 1, 1, 1, 0, 0, 0, 0], [2, 1, 1, 2, 3, 3] ],
			[ '6-46', PCS[0, 1, 2, 4, 6, 9], 10, '24', [6, 2, 3, 3, 3, 3, 1], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 2, 2, 3, 3] ],
			[ '6-47', PCS[0, 1, 2, 4, 7, 9], 36, '25', [6, 2, 3, 3, 2, 4, 1], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 2, 3, 2, 3] ],
			[ '6-48', PCS[0, 1, 2, 5, 7, 9], 37, '26', [6, 2, 3, 2, 3, 4, 1], [1, 1, 0, 0, 0, 0, 0, 0], [1, 1, 3, 2, 2, 3] ],
			[ '6-49', PCS[0, 1, 3, 4, 7, 9], 49, '28', [6, 2, 2, 4, 3, 2, 2], [1, 1, 1, 1, 0, 0, 0, 0], [1, 2, 1, 3, 2, 3] ],
			[ '6-50', PCS[0, 1, 4, 6, 7, 9], 13, '29', [6, 2, 2, 4, 2, 3, 2], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 1, 2, 3] ],

			[ '7-1', PCS[0, 1, 2, 3, 4, 5, 6], 35, nil, [7, 6, 5, 4, 3, 2, 1], [1, 1, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 6] ],
			[ '7-2', PCS[0, 1, 2, 3, 4, 5, 7], 23, nil, [7, 5, 5, 4, 3, 3, 1], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 2, 5] ],
			[ '7-3', PCS[0, 1, 2, 3, 4, 5, 8], 27, nil, [7, 5, 4, 4, 4, 3, 1], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 3, 4] ],
			[ '7-4', PCS[0, 1, 2, 3, 4, 6, 7], 29, nil, [7, 5, 4, 4, 3, 3, 2], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 2, 1, 5] ],
			[ '7-5', PCS[0, 1, 2, 3, 5, 6, 7], 14, nil, [7, 5, 4, 3, 3, 4, 2], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 2, 1, 1, 5] ],
			[ '7-6', PCS[0, 1, 2, 3, 4, 7, 8], 20, nil, [7, 5, 3, 3, 4, 4, 2], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 3, 1, 4] ],
			[ '7-7', PCS[0, 1, 2, 3, 6, 7, 8], 7, nil, [7, 5, 3, 2, 3, 5, 3], [1, 0, 0, 1, 0, 0, 0, 0], [1, 1, 1, 3, 1, 1, 4] ],
			[ '7-8', PCS[0, 2, 3, 4, 5, 6, 8], 34, nil, [7, 4, 5, 4, 4, 2, 2], [1, 1, 0, 0, 0, 0, 0, 0], [2, 1, 1, 1, 1, 2, 4] ],
			[ '7-9', PCS[0, 1, 2, 3, 4, 6, 8], 24, nil, [7, 4, 5, 3, 4, 3, 2], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 2, 2, 4] ],
			[ '7-10', PCS[0, 1, 2, 3, 4, 6, 9], 25, nil, [7, 4, 4, 5, 3, 3, 2], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 2, 3, 3] ],
			[ '7-11', PCS[0, 1, 3, 4, 5, 6, 8], 11, nil, [7, 4, 4, 4, 4, 4, 1], [1, 0, 1, 0, 0, 0, 0, 0], [1, 2, 1, 1, 1, 2, 4] ],
			[ '7-12', PCS[0, 1, 2, 3, 4, 7, 9], 12, '36', [7, 4, 4, 4, 3, 4, 2], [1, 1, 1, 1, 0, 0, 0, 0], [1, 1, 1, 1, 3, 2, 3] ],
			[ '7-13', PCS[0, 1, 2, 4, 5, 6, 8], 30, nil, [7, 4, 4, 3, 5, 3, 2], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 2, 1, 1, 2, 4] ],
			[ '7-14', PCS[0, 1, 2, 3, 5, 7, 8], 5, nil, [7, 4, 4, 3, 3, 5, 2], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 2, 2, 1, 4] ],
			[ '7-15', PCS[0, 1, 2, 4, 6, 7, 8], 15, nil, [7, 4, 4, 2, 4, 4, 3], [1, 1, 1, 1, 0, 0, 0, 0], [1, 1, 2, 2, 1, 1, 4] ],
			[ '7-16', PCS[0, 1, 2, 3, 5, 6, 9], 32, nil, [7, 4, 3, 5, 4, 3, 2], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 2, 1, 3, 3] ],
			[ '7-17', PCS[0, 1, 2, 4, 5, 6, 9], 37, '37', [7, 4, 3, 4, 5, 4, 1], [1, 1, 0, 0, 0, 0, 0, 0], [1, 1, 2, 1, 1, 3, 3] ],
			[ '7-18', PCS[0, 1, 2, 3, 5, 8, 9], 38, '38', [7, 4, 3, 4, 4, 4, 2], [1, 0, 0, 0, 0, 0, 0, 0], [1, 3, 1, 1, 1, 2, 3] ],
			[ '7-19', PCS[0, 1, 2, 3, 6, 7, 9], 19, nil, [7, 4, 3, 4, 3, 4, 3], [1, 0, 0, 1, 0, 0, 0, 0], [1, 1, 1, 3, 1, 2, 3] ],
			[ '7-20', PCS[0, 1, 2, 4, 7, 8, 9], 6, nil, [7, 4, 3, 3, 4, 5, 2], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 2, 3, 1, 1, 3] ],
			[ '7-21', PCS[0, 1, 2, 4, 5, 8, 9], 21, nil, [7, 4, 2, 4, 6, 4, 1], [1, 0, 1, 0, 0, 0, 0, 0], [1, 1, 2, 1, 3, 1, 3] ],
			[ '7-22', PCS[0, 1, 2, 5, 6, 8, 9], 22, nil, [7, 4, 2, 4, 5, 4, 2], [1, 1, 1, 1, 0, 0, 0, 0], [1, 1, 3, 1, 2, 1, 3] ],
			[ '7-23', PCS[0, 2, 3, 4, 5, 7, 9], 2, nil, [7, 3, 5, 4, 3, 5, 1], [1, 0, 0, 0, 0, 0, 0, 0], [2, 1, 1, 1, 2, 2, 3] ],
			[ '7-24', PCS[0, 1, 2, 3, 5, 7, 9], 9, nil, [7, 3, 5, 3, 4, 4, 2], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 2, 2, 2, 3] ],
			[ '7-25', PCS[0, 2, 3, 4, 6, 7, 9], 10, nil, [7, 3, 4, 5, 3, 4, 2], [1, 0, 0, 0, 0, 0, 0, 0], [2, 1, 1, 2, 1, 2, 3] ],
			[ '7-26', PCS[0, 1, 3, 4, 5, 7, 9], 26, nil, [7, 3, 4, 4, 5, 3, 2], [1, 0, 1, 0, 0, 0, 0, 0], [1, 2, 1, 1, 2, 2, 3] ],
			[ '7-27', PCS[0, 1, 2, 4, 5, 7, 9], 3, nil, [7, 3, 4, 4, 4, 5, 1], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 2, 1, 2, 2, 3] ],
			[ '7-28', PCS[0, 1, 3, 5, 6, 7, 9], 28, nil, [7, 3, 4, 4, 4, 3, 3], [1, 0, 0, 1, 0, 0, 0, 0], [1, 2, 2, 1, 1, 2, 3] ],
			[ '7-29', PCS[0, 1, 2, 4, 6, 7, 9], 4, nil, [7, 3, 4, 4, 3, 5, 2], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 2, 2, 1, 2, 3] ],
			[ '7-30', PCS[0, 1, 2, 4, 6, 8, 9], 13, nil, [7, 3, 4, 3, 5, 4, 2], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 2, 2, 2, 1, 3] ],
			[ '7-31', PCS[0, 1, 3, 4, 6, 7, 9], 31, nil, [7, 3, 3, 6, 3, 3, 3], [1, 0, 0, 1, 0, 0, 0, 0], [1, 2, 1, 2, 1, 2, 3] ],
			[ '7-32', PCS[0, 1, 3, 4, 6, 8, 9], 16, nil, [7, 3, 3, 5, 4, 4, 2], [1, 0, 0, 0, 0, 0, 0, 0], [1, 2, 1, 2, 2, 1, 3] ],
			[ '7-33', PCS[0, 1, 2, 4, 6, 8, 10], 33, nil, [7, 2, 6, 2, 6, 2, 3], [1, 1, 1, 1, 0, 0, 0, 0], [1, 1, 2, 2, 2, 2, 2] ],
			[ '7-34', PCS[0, 1, 3, 4, 6, 8, 10], 8, nil, [7, 2, 5, 4, 4, 4, 2], [1, 1, 0, 0, 0, 0, 0, 0], [1, 2, 1, 2, 2, 2, 2] ],
			[ '7-35', PCS[0, 1, 3, 5, 6, 8, 10], 1, nil, [7, 2, 5, 4, 3, 6, 1], [1, 1, 0, 0, 0, 0, 0, 0], [1, 2, 2, 1, 2, 2, 2] ],
			[ '7-36', PCS[0, 1, 2, 3, 5, 6, 8], 36, '12', [7, 4, 4, 4, 3, 4, 2], [1, 0, 0, 1, 0, 0, 0, 0], [1, 1, 1, 2, 1, 2, 4] ],
			[ '7-37', PCS[0, 1, 3, 4, 5, 7, 8], 17, '17', [7, 4, 3, 4, 5, 4, 1], [1, 1, 0, 0, 0, 0, 0, 0], [1, 2, 1, 1, 2, 1, 4] ],
			[ '7-38', PCS[0, 1, 2, 4, 5, 7, 8], 18, '18', [7, 4, 3, 4, 4, 4, 2], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 2, 1, 2, 1, 4] ],

			[ '8-1', PCS[0, 1, 2, 3, 4, 5, 6, 7], 23, nil, [8, 7, 6, 5, 4, 4, 2], [1, 1, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 1, 5] ],
			[ '8-2', PCS[0, 1, 2, 3, 4, 5, 6, 8], 22, nil, [8, 6, 6, 5, 5, 4, 2], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 2, 4] ],
			[ '8-3', PCS[0, 1, 2, 3, 4, 5, 6, 9], 26, nil, [8, 6, 5, 6, 5, 4, 2], [1, 1, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 3, 3] ],
			[ '8-4', PCS[0, 1, 2, 3, 4, 5, 7, 8], 14, nil, [8, 6, 5, 5, 5, 5, 2], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 2, 1, 4] ],
			[ '8-5', PCS[0, 1, 2, 3, 4, 6, 7, 8], 16, nil, [8, 6, 5, 4, 5, 5, 3], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 2, 1, 1, 4] ],
			[ '8-6', PCS[0, 1, 2, 3, 5, 6, 7, 8], 6, nil, [8, 6, 5, 4, 4, 6, 3], [1, 1, 1, 1, 0, 0, 0, 0], [1, 1, 1, 2, 1, 1, 1, 4] ],
			[ '8-7', PCS[0, 1, 2, 3, 4, 5, 8, 9], 20, nil, [8, 6, 4, 5, 6, 5, 2], [1, 1, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 3, 1, 3] ],
			[ '8-8', PCS[0, 1, 2, 3, 4, 7, 8, 9], 8, nil, [8, 6, 4, 4, 5, 6, 3], [1, 1, 1, 1, 0, 0, 0, 0], [1, 1, 1, 1, 3, 1, 1, 3] ],
			[ '8-9', PCS[0, 1, 2, 3, 6, 7, 8, 9], 9, nil, [8, 6, 4, 4, 4, 6, 4], [2, 2, 2, 2, 0, 0, 0, 0], [1, 1, 1, 3, 1, 1, 1, 3] ],
			[ '8-10', PCS[0, 2, 3, 4, 5, 6, 7, 9], 10, nil, [8, 5, 6, 6, 4, 5, 2], [1, 1, 1, 1, 0, 0, 0, 0], [2, 1, 1, 1, 1, 1, 2, 3] ],
			[ '8-11', PCS[0, 1, 2, 3, 4, 5, 7, 9], 11, nil, [8, 5, 6, 5, 5, 5, 2], [1, 0, 1, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 2, 2, 3] ],
			[ '8-12', PCS[0, 1, 3, 4, 5, 6, 7, 9], 27, nil, [8, 5, 5, 6, 5, 4, 3], [1, 0, 0, 0, 0, 0, 0, 0], [1, 2, 1, 1, 1, 1, 2, 3] ],
			[ '8-13', PCS[0, 1, 2, 3, 4, 6, 7, 9], 13, nil, [8, 5, 5, 6, 4, 5, 3], [1, 0, 0, 1, 0, 0, 0, 0], [1, 1, 1, 1, 2, 1, 2, 3] ],
			[ '8-14', PCS[0, 1, 2, 4, 5, 6, 7, 9], 4, nil, [8, 5, 5, 5, 5, 6, 2], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 2, 1, 1, 1, 2, 3] ],
			[ '8-15', PCS[0, 1, 2, 3, 4, 6, 8, 9], 29, '29', [8, 5, 5, 5, 5, 5, 3], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 2, 2, 1, 3] ],
			[ '8-16', PCS[0, 1, 2, 3, 5, 7, 8, 9], 5, nil, [8, 5, 5, 4, 5, 6, 3], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 2, 2, 1, 1, 3] ],
			[ '8-17', PCS[0, 1, 3, 4, 5, 6, 8, 9], 17, nil, [8, 5, 4, 6, 6, 5, 2], [1, 1, 1, 1, 0, 0, 0, 0], [1, 2, 1, 1, 1, 2, 1, 3] ],
			[ '8-18', PCS[0, 1, 2, 3, 5, 6, 8, 9], 18, nil, [8, 5, 4, 6, 5, 5, 3], [1, 0, 0, 1, 0, 0, 0, 0], [1, 1, 1, 2, 1, 2, 1, 3] ],
			[ '8-19', PCS[0, 1, 2, 4, 5, 6, 8, 9], 19, nil, [8, 5, 4, 5, 7, 5, 2], [1, 0, 1, 0, 0, 0, 0, 0], [1, 1, 2, 1, 1, 2, 1, 3] ],
			[ '8-20', PCS[0, 1, 2, 4, 5, 7, 8, 9], 7, nil, [8, 5, 4, 5, 6, 6, 2], [1, 1, 0, 0, 0, 0, 0, 0], [1, 1, 2, 1, 2, 1, 1, 3] ],
			[ '8-21', PCS[0, 1, 2, 3, 4, 6, 8, 10], 21, nil, [8, 4, 7, 4, 6, 4, 3], [1, 1, 1, 1, 0, 0, 0, 0], [1, 1, 1, 1, 2, 2, 2, 2] ],
			[ '8-22', PCS[0, 1, 2, 3, 5, 6, 8, 10], 2, nil, [8, 4, 6, 5, 5, 6, 2], [1, 0, 0, 0, 0, 0, 0], [1, 1, 1, 2, 1, 2, 2, 2] ],
			[ '8-23', PCS[0, 1, 2, 3, 5, 7, 8, 10], 1, nil, [8, 4, 6, 5, 4, 7, 2], [1, 1, 0, 0, 0, 0, 0, 0], [1, 1, 1, 2, 2, 1, 2, 2] ],
			[ '8-24', PCS[0, 1, 2, 4, 5, 6, 8, 10], 24, nil, [8, 4, 6, 4, 7, 4, 3], [1, 1, 1, 1, 0, 0, 0, 0], [1, 1, 2, 1, 1, 2, 2, 2] ],
			[ '8-25', PCS[0, 1, 2, 4, 6, 7, 8, 10], 25, nil, [8, 4, 6, 4, 6, 4, 4], [2, 2, 2, 2, 0, 0, 0, 0], [1, 1, 2, 2, 1, 1, 2, 2] ],
			[ '8-26', PCS[0, 1, 2, 4, 5, 7, 9, 10], 3, nil, [8, 4, 5, 6, 5, 6, 2], [1, 1, 0, 0, 0, 0, 0, 0], [1, 1, 2, 1, 2, 2, 1, 2] ],
			[ '8-27', PCS[0, 1, 2, 4, 5, 7, 8, 10], 12, nil, [8, 4, 5, 6, 5, 5, 3], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 2, 1, 2, 1, 2, 2] ],
			[ '8-28', PCS[0, 1, 3, 4, 6, 7, 9, 10], 28, nil, [8, 4, 4, 8, 4, 4, 4], [4, 4, 4, 4, 0, 0, 0, 0], [1, 2, 1, 2, 1, 2, 1, 2] ],
			[ '8-29', PCS[0, 1, 2, 3, 5, 6, 7, 9], 15, '15', [8, 5, 5, 5, 5, 5, 3], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 2, 1, 1, 2, 3] ],

			[ '9-1', PCS[0, 1, 2, 3, 4, 5, 6, 7, 8], 9, nil, [9, 8, 7, 6, 6, 6, 3], [1, 1, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 1, 1, 4] ],
			[ '9-2', PCS[0, 1, 2, 3, 4, 5, 6, 7, 9], 7, nil, [9, 7, 7, 7, 6, 6, 3], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 1, 2, 3] ],
			[ '9-3', PCS[0, 1, 2, 3, 4, 5, 6, 8, 9], 11, nil, [9, 7, 6, 7, 7, 6, 3], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 2, 1, 3] ],
			[ '9-4', PCS[0, 1, 2, 3, 4, 5, 7, 8, 9], 4, nil, [9, 7, 6, 6, 7, 7, 3], [1, 0, 1, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 2, 1, 1, 3] ],
			[ '9-5', PCS[0, 1, 2, 3, 4, 6, 7, 8, 9], 5, nil, [9, 7, 6, 6, 6, 7, 4], [1, 0, 0, 1, 0, 0, 0, 0], [1, 1, 1, 1, 2, 1, 1, 1, 3] ],
			[ '9-6', PCS[0, 1, 2, 3, 4, 5, 6, 8, 10], 6, nil, [9, 6, 8, 6, 7, 6, 3], [1, 1, 1, 1, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 2, 2, 2] ],
			[ '9-7', PCS[0, 1, 2, 3, 4, 5, 7, 8, 10], 2, nil, [9, 6, 7, 7, 6, 7, 3], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 2, 1, 2, 2] ],
			[ '9-8', PCS[0, 1, 2, 3, 4, 6, 7, 8, 10], 8, nil, [9, 6, 7, 6, 7, 6, 4], [1, 0, 0, 1, 0, 0, 0, 0], [1, 1, 1, 1, 2, 1, 1, 2, 2] ],
			[ '9-9', PCS[0, 1, 2, 3, 5, 6, 7, 8, 10], 1, nil, [9, 6, 7, 6, 6, 8, 3], [1, 1, 0, 0, 0, 0, 0, 0], [1, 1, 1, 2, 1, 1, 1, 2, 2] ],
			[ '9-10', PCS[0, 1, 2, 3, 4, 6, 7, 9, 10], 10, nil, [9, 6, 6, 8, 6, 6, 4], [1, 1, 1, 1, 0, 0, 0, 0], [1, 1, 1, 1, 2, 1, 2, 1, 2] ],
			[ '9-11', PCS[0, 1, 2, 3, 5, 6, 7, 9, 10], 3, nil, [9, 6, 6, 7, 7, 7, 3], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 2, 1, 1, 2, 1, 2] ],
			[ '9-12', PCS[0, 1, 2, 4, 5, 6, 8, 9, 10], 12, nil, [9, 6, 6, 6, 9, 6, 3], [3, 3, 3, 3, 0, 0, 0, 0], [1, 1, 2, 1, 1, 2, 1, 1, 2] ],

			[ '10-1', PCS[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], 5, nil, [10, 9, 8, 8, 8, 8, 4], [1, 1, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 1, 1, 1, 3] ],
			[ '10-2', PCS[0, 1, 2, 3, 4, 5, 6, 7, 8, 10], 2, nil, [10, 8, 9, 8, 8, 8, 4], [1, 1, 1, 1, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 1, 1, 2, 2] ],
			[ '10-3', PCS[0, 1, 2, 3, 4, 5, 6, 7, 9, 10], 3, nil, [10, 8, 8, 9, 8, 8, 4], [1, 1, 1, 1, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 1, 2, 1, 2] ],
			[ '10-4', PCS[0, 1, 2, 3, 4, 5, 6, 8, 9, 10], 4, nil, [10, 8, 8, 8, 9, 8, 4], [1, 1, 1, 1, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 2, 1, 1, 2] ],
			[ '10-5', PCS[0, 1, 2, 3, 4, 5, 7, 8, 9, 10], 1, nil, [10, 8, 8, 8, 8, 9, 4], [1, 1, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 2, 1, 1, 1, 2] ],
			[ '10-6', PCS[0, 1, 2, 3, 4, 6, 7, 8, 9, 10], 6, nil, [10, 8, 8, 8, 8, 8, 5], [2, 2, 2, 2, 0, 0, 0, 0], [1, 1, 1, 1, 2, 1, 1, 1, 1, 2] ],

			[ '11-1', PCS[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], 1, nil, [11, 10, 10, 10, 10, 10, 5], [1, 1, 1, 1, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2] ],

			[ '12-1', PCS[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], 1, nil, [12, 12, 12, 12, 12, 12, 6], [12, 12, 12, 12, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] ]
		];

		indexFromName = IdentityDictionary.new;
		indexFromPF = IdentityDictionary.new;

		table.do({ arg i, j;
			indexFromName.put(i.at(0), j);
			indexFromPF.put(i.at(1).pcsHash, j);
		});
		}; // bench;
		"PCSLib-SC: SCTable loaded in % seconds".format(time).postln;
	}
}

