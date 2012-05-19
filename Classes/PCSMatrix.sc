// pcslib-sc 2011
// Combinatory Matrix

PCSMatrix {
	var <type;
	var <matrix;
	var <vnorm, <hnorm;

	*newFromArray { arg arr, type;
		^this.new.prCopyFromArray(arr, type);
	}

	prCopyFromArray { arg arr, t;
		// check si los nodos son pcs
		matrix = arr.deepCopy;
		hnorm = arr.at(0).deepCopy;
		vnorm = arr.flop.at(0).deepCopy;
		type = t;
	}

	*roman { arg norm;
		^super.new.initMatrix(norm, nil, \roman);
	}

	*t1a { arg norm;
		^super.new.initMatrix(norm, nil, \t1a);
	}

	*t1b { arg norm;
		^super.new.initMatrix(norm, nil, \t1b);
	}

	*t2 { arg hnorm, vnorm;
		^super.new.initMatrix(hnorm, vnorm, \t2);
	}

	*fromChain { arg pcsChain, normParts = 2;
		^super.new.initMatrix(pcsChain.asArray.clump(normParts), nil, \chain);
	}

	*opcy { arg norm, op;
		^super.new.initOpcyMatrix(norm, op, \opcy);
	}

	initMatrix { arg hn, vn, t;
		matrix = [];
		type = t;

		if(hn.class == PCS, {
			hn = hn.asArray.clump(1).collect({ arg i; i.as(PCS) });
		});
		if(vn.class == PCS, {
			vn = vn.asArray.clump(1).collect({ arg i; i.as(PCS) });
		});

		switch(type,
			\roman, {
				hnorm = vnorm = hn;
				matrix = hnorm.size.collect({ arg i;
					hnorm.rotate(i.neg);
				});
			},
			\t1a, {
				hnorm = vnorm = hn;
				matrix = hnorm.collect({ arg i;
					hnorm.collect({ arg j;
						(j.asArray + i.asArray).as(PCS);
					});
				});
			},
			\t1b, {
				hnorm = vnorm = hn;
				matrix = hnorm.collect({ arg i;
					hnorm.collect({ arg j;
						(j.asArray + i.i.asArray).as(PCS);
					});
				});
			},
			\t2, {
				hnorm = hn;
				vnorm = vn ? hn;
				matrix = vnorm.collect({ arg i;
					hnorm.collect({ arg j;
						(j.asArray + i.asArray).as(PCS);
					});
				});
			},
			\chain, {
				matrix = hn.collect({ arg i, j;
					(i ++ PCS[].dup(hn.size - i.size)).rotate(j);
				});
				hnorm = hn.at(0);
				vnorm = matrix.flop.at(0).reject(_.isEmpty);
			}
		);
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

	performOnMatrix { arg op ...args;
		var arr = matrix.collect({ arg row;
			row.collect(_.perform(op, *args));
		});
		^PCSMatrix.newFromArray(arr, this.type);
	}

	// cm_trans
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
			^PCSMatrix.newFromArray(arr, this.type);
		}, {
			matrix.do({ arg row, i;
				row.reverseDo({ arg pcs, j;
					arr[j][i] = pcs.copy;
				});
			});
			^PCSMatrix.newFromArray(arr, this.type);
		});
	}

	rD {
		// ver qué es, tal vez es invX comb invY?
	}

	invX {
		var arr = matrix.reverse;
		^PCSMatrix.newFromArray(arr, this.type);
	}

	invY {
		var arr = matrix.collect({ arg row;
			row.reverse;
		});
		^PCSMatrix.newFromArray(arr, this.type);
	}

	eRow { arg r1, r2;
		var arr = matrix.deepCopy; // FIXME: copy, copy...
		var aux = arr[r1];
		arr[r1] = arr[r2];
		arr[r2] = aux;
		^PCSMatrix.newFromArray(arr, this.type);
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
		^PCSMatrix.newFromArray(arr, this.type);
	}

	// swap
	// cm

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

