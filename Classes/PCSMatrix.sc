// pcslib-sc 2011
// Combinatory Matrix

PCSMatrix {
	var <type;
	var <matrix;
	var <vnorm, <hnorm;

	*fromArray { arg arr, type = \fromArray;
		^this.new.initMatrixFromArray(arr, type);
	}

	initMatrixFromArray { arg arr, t;
		matrix = arr.collect({ arg i;
			i.collect({ arg j;
				j.asArray.as(PCS);
			})
		});
		hnorm = matrix.at(0);
		vnorm = matrix.flop.at(0);
		type = t;
	}

	*roman { arg norm;
		^super.new.initRomanMatrix(norm);
	}

	initRomanMatrix { arg hn;
		type = \roman;

		if(hn.class == PCS, {
			hn = hn.asArray.clump(1).collect({ arg i; i.as(PCS) });
		});

		hnorm = vnorm = hn;
		matrix = hnorm.size.collect({ arg i;
			hnorm.rotate(i.neg);
		});
	}

	*t1a { arg norm;
		^super.new.initTypeMatrix(norm, nil, \t1a);
	}

	*t1b { arg norm;
		^super.new.initTypeMatrix(norm, nil, \t1b);
	}

	*t2 { arg hnorm, vnorm;
		^super.new.initTypeMatrix(hnorm, vnorm, \t2);
	}

	initTypeMatrix { arg hn, vn, t;
		var auxOp = \copy; // self

		type = t;

		if(hn.class == PCS, {
			hn = hn.asArray.clump(1).collect({ arg i; i.as(PCS) });
		});
		if(vn.class == PCS, {
			vn = vn.asArray.clump(1).collect({ arg i; i.as(PCS) });
		});

		hnorm = hn;
		vnorm = vn ? hn;
		if(type == \t1b, { auxOp = \i });

		matrix = vnorm.collect({ arg i;
			hnorm.collect({ arg j;
				(j.asArray + i.perform(auxOp).asArray).as(PCS);
			});
		});
	}

	*fromChain { arg pcsChain, normParts = 2;
		^super.new.initMatrix(pcsChain.asArray.clump(normParts));
	}

	initChainMatrix { arg hn;
		type = \chain;

		matrix = hn.collect({ arg i, j;
			(i ++ PCS[].dup(hn.size - i.size)).rotate(j);
		});
		hnorm = hn.at(0);
		vnorm = matrix.flop.at(0).reject(_.isEmpty);
	}

	*opcy { arg norm, op;
		^super.new.initOpcyMatrix(norm, op, \opcy);
	}

	initOpcyMatrix { arg norm, op, t;
		var transp, size;

		switch(op.asSymbol,
			'T2/A', {
				transp = 2;
				size = 6;
			},
			'T3/9', {
				transp = 3;
				size = 4;
			},
			'T4/8', {
				transp = 4;
				size = 3;
			},
			'T6/TI', {
				transp = 6;
				size = 2;
			},
			{ Error("PCSMatrix invalid op").throw; }
		);

		matrix = [];
		type = (t ++ " " ++ op).asSymbol;
		hnorm = vnorm = norm;

		if(norm.class == PCS, {
			matrix = size.collect({ arg i;
				var ret;
				ret = ([norm] ++ PCS[].dup(size - 1)).rotate(i);
				norm = norm.t(transp);
				ret;
			});
		}, {
			matrix = size.collect({ arg i;
				var ret;
				ret = (norm ++ PCS[].dup(size - norm.size)).rotate(i);
				norm = norm.collect(_.t(transp));
				ret;
			});
		});
	}

	// cm_trans
	performOnMatrix { arg op ...args;
		var arr = matrix.collect({ arg row;
			row.collect(_.perform(op, *args));
		});
		^PCSMatrix.fromArray(arr, this.type);
	}

	i { ^this.performOnMatrix(\i); }
	t { arg n = 0; ^this.performOnMatrix(\t, n); }
	m { arg n = 5; ^this.performOnMatrix(\m, n); }

	r90 { arg clockwise = false;
		var arr = Array.fill2D(matrix.at(0).size, matrix.size);

		if(clockwise, {
			matrix.reverseDo({ arg row, i;
				row.do({ arg pcs, j;
					arr[j][i] = pcs.copy;
				});
			});
			^PCSMatrix.fromArray(arr, this.type);
		}, {
			matrix.do({ arg row, i;
				row.reverseDo({ arg pcs, j;
					arr[j][i] = pcs.copy;
				});
			});
			^PCSMatrix.fromArray(arr, this.type);
		});
	}

	rD {
		// ver qué es, tal vez es invX comb invY?
	}

	invX {
		var arr = matrix.reverse;
		^PCSMatrix.fromArray(arr, this.type);
	}

	invY {
		var arr = matrix.collect({ arg row;
			row.reverse;
		});
		^PCSMatrix.fromArray(arr, this.type);
	}

	eRow { arg r1, r2;
		var arr = matrix.deepCopy; // FIXME: copy, copy...
		var aux = arr[r1];
		arr[r1] = arr[r2];
		arr[r2] = aux;
		^PCSMatrix.fromArray(arr, this.type);
	}

	eCol { arg c1, c2;
		var arr = matrix.deepCopy; // FIXME: copy, copy...
		var aux;
		arr = arr.collect({ arg i;
			aux = i[c1];
			i[c1] = i[c2];
			i[c2] = aux;
			i;
		});
		^PCSMatrix.fromArray(arr, this.type);
	}

	//swap

	// cm_ana
	//frag
	//spar
	hist {
		var pfa = Array.fill(12, 0);
		matrix.do({ arg row;
			row.do({ arg pcs;
				pcs.do({ arg i; pfa[i] = pfa[i] + 1 });
			});
		});
		^pfa;
	}

	// cm_2pcs
	pcsAtPos { arg x, y;
		^this.matrix[x][y];
	}

	pcsAtRow { arg n;
		var ret = PCS[];
		this.matrix[n].do({ arg i; ret = ret union: i });
		^ret;
	}

	pcsAtCol { arg n;
		var ret = PCS[];
		this.matrix.do({ arg i; ret = ret union: i[n] });
		^ret;
	}

	pcsAtAll {
		var ret = PCS[];
		this.matrix.flat.do({ arg i; ret = ret union: i });
		^ret;
	}

	/* from Matrix
	printOn { arg stream;
		if (stream.atLimit) { ^this };
		stream << this.class.name << "[ " ;
		matrix.do({ arg row, i;
			if (stream.atLimit) { ^this };
			if (i != 0, { stream.comma; });
			stream << "\n";
			stream.tab;
			row.printOn(stream);
		});
		stream << "\n";
		stream << " ]" ;
	}
	*/
}

