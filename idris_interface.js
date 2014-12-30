var IdrisInterface = function(element) {
	this.callbacks_ = [];
	this.events_ = [];
	this.element_ = element;

	var that = this;
	element.addEventListener('keydown', function(e) {that.on_keydown_(e)});
}

IdrisInterface.prototype.on_keydown_ = function(e) {
	if (this.callbacks_.length > 0) {
		this.callbacks_.shift()(e['keyCode']);
	} else {
		this.events_.push(e);
	}
}

IdrisInterface.prototype.get_next_event = function(callback) {
	if (this.events_.length > 0) {
		var e = this.events_.shift();
		callback(this.events_.shift());	
	} else {
		this.callbacks_.push(callback);
	}	
}

IdrisInterface.prototype.show = function(str) {
	for (var i = 0; i < 4; i++) {
		for (var j = 0; j < 4; j++) {
			console.log("" + i + "" + j)
			var value = Math.pow(2, str[4 * i + j]);
			document.getElementById("" + i + "" + j).innerHTML = value || ''
		}
	}
}

var idris_interface = new IdrisInterface(document.getElementById('game-area'));
